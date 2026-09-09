import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_pyx_pxy_pxx_pyx_Equation1061 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e43 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) := by
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
      have b0e45 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
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
      have b0e341 : (M.op x y) = (k x y) := by
        first
        | (have j0 := b0e43 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e805 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b0e45 (σ x)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e807 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e805
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e805
        | exact resolve b0e805 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e805
      have b0e823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e807
           have i₂ := b0e341
           grind)
        | exact superpose b0e341 b0e807
        | exact resolve b0e807 b0e341
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e341 b0e807
      have b0e827 : False := by grind
      exact b0e827
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : (M.op x x) = (M.op y y) := by grind
        have b1e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e54 (σ X0)
             grind)
          | exact superpose b1e54 b1e18
          | exact resolve b1e18 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e57 X0
             have i₂ := b1e54 X0
             grind)
          | exact superpose b1e54 b1e57
          | exact resolve b1e57 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54 b1e57
        have b1e286 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e64 y
             grind)
          | exact superpose b1e64 b1e21
          | exact resolve b1e21 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e295 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e286
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e286
          | exact resolve b1e286 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e286
        have b1e299 : False := by grind
        exact b1e299
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x x) = (M.op y y) := by grind
        have b2e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
        have b2e63 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e56 X0
             have i₂ := b2e53 X0
             grind)
          | exact superpose b2e53 b2e56
          | exact resolve b2e56 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53 b2e56
        have b2e179 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e63 y
             grind)
          | exact superpose b2e63 b2e21
          | exact resolve b2e21 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e187 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e179
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e179
          | exact resolve b2e179 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e179
        have b2e190 : False := by grind
        exact b2e190
  · rcases eq_or_ne (M.op x x) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op x x) ≠ (M.op y y) := by grind
        have b3e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
        have b3e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e57 X0
             have i₂ := b3e54 X0
             grind)
          | exact superpose b3e54 b3e57
          | exact resolve b3e57 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54 b3e57
        have b3e233 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e64 y
             grind)
          | exact superpose b3e64 b3e22
          | exact resolve b3e22 b3e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e241 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e233
             have i₂ := b3e64 x
             grind)
          | exact superpose b3e64 b3e233
          | exact resolve b3e233 b3e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e64 b3e233
        have b3e301 : (M.op y y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b3e13 (M.op y y)
             have i₂ := b3e241
             grind)
          | exact superpose b3e241 b3e13
          | exact resolve b3e13 b3e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e241
        have b3e302 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b3e301
             have i₂ := b3e13 (M.op x x)
             grind)
          | exact superpose b3e13 b3e301
          | exact resolve b3e301 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e301
        have b3e308 : False := by grind
        exact b3e308
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op x x) ≠ (M.op y y) := by grind
          have b4e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
          have b4e78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e69 X0
               have i₂ := b4e66 X0
               grind)
            | exact superpose b4e66 b4e69
            | exact resolve b4e69 b4e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66 b4e69
          have b4e136 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e141 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e18 (σ X1) (σ X0)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X0) (σ X1)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e148 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e136 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e136
          have b4e149 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e148 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e148
          have b4e152 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e141 X0 X1
               have i₂ := b4e78 X1
               grind)
            | exact superpose b4e78 b4e141
            | (have j0 := b4e141 X0 X1
               grind)
            | exact resolve b4e141 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e141
          have b4e165 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e152 X0 X1
               have i₂ := b4e78 X0
               grind)
            | exact superpose b4e78 b4e152
            | (have j0 := b4e152 X0 X1
               grind)
            | exact resolve b4e152 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e152
          have b4e175 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e165 X0 X1
               have i₂ := b4e78 X1
               grind)
            | exact superpose b4e78 b4e165
            | (have j0 := b4e165 X0 X1
               grind)
            | exact resolve b4e165 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e165
          have b4e186 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e78 y
               grind)
            | exact superpose b4e78 b4e23
            | exact resolve b4e23 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e194 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e186
               have i₂ := b4e78 x
               grind)
            | exact superpose b4e78 b4e186
            | exact resolve b4e186 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e186
          have b4e1113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e149 (σ X0) (σ X1)
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e149
            | (have j0 := b4e149 (σ X0) (σ X1)
               grind)
            | exact resolve b4e149 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1236 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e149 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e149
          have b4e1240 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e1236 X0 X1
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e1236 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e1236 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e1236 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e1236 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1236
          have b4e1291 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1113 X0 X1
               have i₂ := b4e78 X1
               grind)
            | exact superpose b4e78 b4e1113
            | (have j0 := b4e1113 X0 X1
               grind)
            | exact resolve b4e1113 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1113
          have b4e1344 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1291 X0 X1
               have i₂ := b4e78 X0
               grind)
            | exact superpose b4e78 b4e1291
            | (have j0 := b4e1291 X0 X1
               grind)
            | exact resolve b4e1291 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1291
          have b4e1358 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1344 X0 X1
               have i₂ := b4e78 X0
               grind)
            | exact superpose b4e78 b4e1344
            | (have j0 := b4e1344 X0 X1
               grind)
            | exact resolve b4e1344 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78 b4e1344
          have b4e3929 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e21
               have i₂ := b4e1240 y X0
               grind)
            | (have i₁ := b4e21
               have i₂ := b4e1240 X0 y
               grind)
            | exact superpose b4e1240 b4e21
            | (have j1 := b4e1240 y X0
               grind)
            | (have r₁ := b4e21
               have r₂ := b4e1240 x y
               grind)
            | (have r₁ := b4e21
               have r₂ := b4e1240 y x
               grind)
            | exact resolve b4e21 b4e1240
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1240
          have b4e4732 : (M.op x y) = (k y x) := by
            first
            | (have j0 := b4e3929 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3929
          have b4e5991 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e175 x y
               grind)
            | exact superpose b4e175 b4e20
            | (have j1 := b4e175 x y
               grind)
            | exact resolve b4e20 b4e175
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e175
          have b4e6031 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b4e5991
               have r₂ := b4e194
               grind)
            | exact resolve b4e5991 b4e194
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5991
          have b4e6137 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e6031
               have i₂ := b4e4732
               grind)
            | exact superpose b4e4732 b4e6031
            | exact resolve b4e6031 b4e4732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6031
          have b4e6138 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
          clear b4e6137
          have b4e6298 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e6138
               grind)
            | exact superpose b4e6138 b4e20
            | exact resolve b4e20 b4e6138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e188401 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ (M.op y y)) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e6138
               have i₂ := b4e1358 y x
               grind)
            | exact superpose b4e1358 b4e6138
            | (have j1 := b4e1358 y x
               grind)
            | exact resolve b4e6138 b4e1358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1358 b4e6138
          have b4e188470 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
          clear b4e188401
          have b4e188475 : (σ (M.op y y)) = (σ (k y x)) := by
            first
            | (have r₁ := b4e188470
               have r₂ := b4e194
               grind)
            | exact resolve b4e188470 b4e194
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e194 b4e188470
          have b4e188500 : (σ (M.op x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e188475
               have i₂ := b4e4732
               grind)
            | exact superpose b4e4732 b4e188475
            | exact resolve b4e188475 b4e4732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4732 b4e188475
          have b4e188516 : False := by grind
          exact b4e188516
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x x) ≠ (M.op y y) := by grind
          have b5e22 : (M.op x x) = (M.op y x) := by grind
          have b5e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
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
               have i₂ := b5e65 (σ X0)
               grind)
            | exact superpose b5e65 b5e19
            | exact resolve b5e19 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e68 X0
               have i₂ := b5e65 X0
               grind)
            | exact superpose b5e65 b5e68
            | exact resolve b5e68 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65 b5e68
          have b5e86 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op x x) = (k x y) := by
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
          have b5e89 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (k x y) := by grind
          clear b5e86
          have b5e91 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e89
               have r₂ := b5e21
               grind)
            | exact resolve b5e89 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e89
          have b5e135 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e18 (σ X1) (σ X0)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e146 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e135 X0 X1
               have i₂ := b5e77 X1
               grind)
            | exact superpose b5e77 b5e135
            | (have j0 := b5e135 X0 X1
               grind)
            | exact resolve b5e135 b5e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e135
          have b5e159 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e146 X0 X1
               have i₂ := b5e77 X0
               grind)
            | exact superpose b5e77 b5e146
            | (have j0 := b5e146 X0 X1
               grind)
            | exact resolve b5e146 b5e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e146
          have b5e169 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e159 X0 X1
               have i₂ := b5e77 X1
               grind)
            | exact superpose b5e77 b5e159
            | (have j0 := b5e159 X0 X1
               grind)
            | exact resolve b5e159 b5e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e159
          have b5e180 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e77 y
               grind)
            | exact superpose b5e77 b5e23
            | exact resolve b5e23 b5e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e188 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e180
               have i₂ := b5e77 x
               grind)
            | exact superpose b5e77 b5e180
            | exact resolve b5e180 b5e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e180
          have b5e5093 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e169 y x
               grind)
            | exact superpose b5e169 b5e24
            | (have j1 := b5e169 y x
               grind)
            | exact resolve b5e24 b5e169
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e169
          have b5e5135 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b5e5093
               have r₂ := b5e188
               grind)
            | exact resolve b5e5093 b5e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e188 b5e5093
          have b5e5238 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e5135
               have i₂ := b5e91
               grind)
            | exact superpose b5e91 b5e5135
            | exact resolve b5e5135 b5e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e91 b5e5135
          have b5e5323 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b5e5238
               have r₂ := b5e77 x
               grind)
            | exact resolve b5e5238 b5e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5238
          have b5e5985 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e5323
               grind)
            | exact superpose b5e5323 b5e24
            | exact resolve b5e24 b5e5323
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5323
          have b5e6003 : False := by grind
          exact b5e6003
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
        have b6e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e53 (σ X0)
             grind)
          | exact superpose b6e53 b6e18
          | exact resolve b6e18 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e63 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e56 X0
             have i₂ := b6e53 X0
             grind)
          | exact superpose b6e53 b6e56
          | exact resolve b6e56 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53 b6e56
        have b6e188 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e63 y
             grind)
          | exact superpose b6e63 b6e22
          | exact resolve b6e22 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e196 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e188
             have i₂ := b6e63 x
             grind)
          | exact superpose b6e63 b6e188
          | exact resolve b6e188 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63 b6e188
        have b6e253 : (M.op y y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (M.op y y)
             have i₂ := b6e196
             grind)
          | exact superpose b6e196 b6e13
          | exact resolve b6e13 b6e196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e196
        have b6e254 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b6e253
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e253
          | exact resolve b6e253 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e253
        have b6e260 : False := by grind
        exact b6e260
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x x) ≠ (M.op y y) := by grind
          have b7e22 : (M.op x x) ≠ (M.op y x) := by grind
          have b7e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
          have b7e77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e68 X0
               have i₂ := b7e65 X0
               grind)
            | exact superpose b7e65 b7e68
            | exact resolve b7e68 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65 b7e68
          have b7e87 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e89 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e87
          have b7e90 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e89
               have r₂ := b7e23
               grind)
            | exact resolve b7e89 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e93 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e90
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e90
            | exact resolve b7e90 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e95 : (σ (k x y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e93
               have i₂ := b7e77 x
               grind)
            | exact superpose b7e77 b7e93
            | exact resolve b7e93 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77 b7e93
          have b7e101 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e95
               grind)
            | exact superpose b7e95 b7e14
            | exact resolve b7e14 b7e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95
          have b7e102 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e101
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e101
            | exact resolve b7e101 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101
          have b7e186 : (M.op x x) = (M.op y x) ∨ (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e102
               grind)
            | exact superpose b7e102 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102
          have b7e187 : (M.op x x) = (M.op y x) ∨ (M.op x x) = (M.op y y) := by grind
          clear b7e186
          have b7e189 : (M.op x x) = (M.op y y) := by
            first
            | (have r₁ := b7e187
               have r₂ := b7e22
               grind)
            | exact resolve b7e187 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e187
          have b7e191 : False := by grind
          exact b7e191
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x x) ≠ (M.op y y) := by grind
          have b8e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e64 (σ X0)
               grind)
            | exact superpose b8e64 b8e19
            | exact resolve b8e19 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e67 X0
               have i₂ := b8e64 X0
               grind)
            | exact superpose b8e64 b8e67
            | exact resolve b8e67 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64 b8e67
          have b8e94 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e76 y
               grind)
            | exact superpose b8e76 b8e23
            | exact resolve b8e23 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e99 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e94
               have i₂ := b8e76 x
               grind)
            | exact superpose b8e76 b8e94
            | exact resolve b8e94 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e94
          have b8e140 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b8e143 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
          have b8e150 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e140 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e140
          have b8e151 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e150 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e150
          have b8e154 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e143 X0 X1
               have i₂ := b8e76 X1
               grind)
            | exact superpose b8e76 b8e143
            | (have j0 := b8e143 X0 X1
               grind)
            | exact resolve b8e143 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e143
          have b8e168 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e154 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e154
            | (have j0 := b8e154 X0 X1
               grind)
            | exact resolve b8e154 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e154
          have b8e178 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e168 X0 X1
               have i₂ := b8e76 X1
               grind)
            | exact superpose b8e76 b8e168
            | (have j0 := b8e168 X0 X1
               grind)
            | exact resolve b8e168 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e168
          have b8e752 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e151 (σ X0) (σ X1)
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e151
            | (have j0 := b8e151 (σ X0) (σ X1)
               grind)
            | exact resolve b8e151 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e858 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e151 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e151
          have b8e862 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e858 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e858 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e858 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e858 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | exact resolve b8e858 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e858
          have b8e902 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e752 X0 X1
               have i₂ := b8e76 X1
               grind)
            | exact superpose b8e76 b8e752
            | (have j0 := b8e752 X0 X1
               grind)
            | exact resolve b8e752 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e752
          have b8e938 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e902 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e902
            | (have j0 := b8e902 X0 X1
               grind)
            | exact resolve b8e902 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e902
          have b8e945 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e938 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e938
            | (have j0 := b8e938 X0 X1
               grind)
            | exact resolve b8e938 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76 b8e938
          have b8e1639 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b8e21
               have i₂ := b8e862 y X0
               grind)
            | (have i₁ := b8e21
               have i₂ := b8e862 X0 y
               grind)
            | exact superpose b8e862 b8e21
            | (have j1 := b8e862 y X0
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e862 x y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e862 y x
               grind)
            | exact resolve b8e21 b8e862
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e862
          have b8e2625 : (M.op x y) = (k y x) := by
            first
            | (have j0 := b8e1639 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1639
          have b8e4980 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e178 x y
               grind)
            | exact superpose b8e178 b8e20
            | (have j1 := b8e178 x y
               grind)
            | exact resolve b8e20 b8e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e178
          have b8e5019 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e4980
               have r₂ := b8e99
               grind)
            | exact resolve b8e4980 b8e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4980
          have b8e5110 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e5019
               have i₂ := b8e2625
               grind)
            | exact superpose b8e2625 b8e5019
            | exact resolve b8e5019 b8e2625
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5019
          have b8e5111 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
          clear b8e5110
          have b8e5256 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e5111
               grind)
            | exact superpose b8e5111 b8e20
            | exact resolve b8e20 b8e5111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e128527 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ (M.op y y)) = (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e5111
               have i₂ := b8e945 y x
               grind)
            | exact superpose b8e945 b8e5111
            | (have j1 := b8e945 y x
               grind)
            | exact resolve b8e5111 b8e945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e945 b8e5111
          have b8e128660 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
          clear b8e128527
          have b8e128698 : (σ (M.op y y)) = (σ (k y x)) := by
            first
            | (have r₁ := b8e128660
               have r₂ := b8e99
               grind)
            | exact resolve b8e128660 b8e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99 b8e128660
          have b8e129038 : (σ (M.op x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e128698
               have i₂ := b8e2625
               grind)
            | exact superpose b8e2625 b8e128698
            | exact resolve b8e128698 b8e2625
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2625 b8e128698
          have b8e129175 : False := by grind
          exact b8e129175

/-- `Equation1681`: `x = (y ◇ x) ◇ ((x ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation1681 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1681 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1681.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e87 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        grind
      have b0e89 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        first
        | (have j0 := b0e87 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87
      have b0e138 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e89 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e89
        | exact resolve b0e89 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e139 : (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e89 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e89
        | exact resolve b0e89 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e89
      have b0e142 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e138
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e138
        | exact resolve b0e138 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e138
      have b0e143 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e142
           have i₂ := b0e139
           grind)
        | exact superpose b0e139 b0e142
        | exact resolve b0e142 b0e139
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e139 b0e142
      have b0e144 : False := by grind
      exact b0e144
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e37 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b1e39 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e37
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e37
          | exact resolve b1e37 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e84 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b1e86 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b1e84 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e84
        have b1e108 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e19
          | exact resolve b1e19 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e133 : (M.op x y) = (k y x) := by
          first
          | (have i₁ := b1e86 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e86
          | exact resolve b1e86 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e86
        have b1e139 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e108
             have i₂ := b1e133
             grind)
          | exact superpose b1e133 b1e108
          | exact resolve b1e108 b1e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e108 b1e133
        have b1e141 : False := by grind
        exact b1e141
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e77 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b2e79 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e77 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77
        have b2e291 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e79 X0
             have i₂ := b2e51 X0 X1
             grind)
          | (have i₁ := b2e79 X0
             have i₂ := b2e51 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e51 b2e79
          | (have j1 := b2e51 X1 X0
             grind)
          | exact resolve b2e79 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e79
        have b2e313 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e291 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e291
        have b2e537 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e313 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e313
        have b2e538 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e537 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e537
        have b2e642 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e538 (σ X0)
             grind)
          | exact superpose b2e538 b2e18
          | exact resolve b2e18 b2e538
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e650 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e642 X0
             have i₂ := b2e538 X0
             grind)
          | exact superpose b2e538 b2e642
          | exact resolve b2e642 b2e538
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e538 b2e642
        have b2e863 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e650 x
             grind)
          | exact superpose b2e650 b2e21
          | exact resolve b2e21 b2e650
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e650
        have b2e890 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e863
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e863
          | exact resolve b2e863 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e863
        have b2e891 : False := by grind
        exact b2e891
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e38 : (M.op x y) = (k y x) := by grind
        have b3e75 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b3e88 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e75
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e75
          | exact resolve b3e75 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e90 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e88
             have i₂ := b3e38
             grind)
          | exact superpose b3e38 b3e88
          | exact resolve b3e88 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e88
        have b3e91 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have r₁ := b3e90
             have r₂ := b3e19
             grind)
          | exact resolve b3e90 b3e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e90
        have b3e100 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b3e91
        have b3e102 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e100
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e100
          | exact resolve b3e100 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e100
        have b3e103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e102
             have i₂ := b3e38
             grind)
          | exact superpose b3e38 b3e102
          | exact resolve b3e102 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38 b3e102
        have b3e104 : False := by grind
        exact b3e104
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e43 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b4e44 : (M.op x y) = (k y x) := by grind
          have b4e46 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e43
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e43
            | exact resolve b4e43 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e47 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e46
               have i₂ := b4e44
               grind)
            | exact superpose b4e44 b4e46
            | exact resolve b4e46 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e46
          have b4e48 : False := by grind
          exact b4e48
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e58 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e85 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e87 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e85 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e288 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e87 X0
               have i₂ := b5e58 X0 X1
               grind)
            | (have i₁ := b5e87 X0
               have i₂ := b5e58 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e58 b5e87
            | (have j1 := b5e58 X1 X0
               grind)
            | exact resolve b5e87 b5e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58 b5e87
          have b5e308 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e288 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e288
          have b5e526 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e308 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e308
          have b5e527 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e526 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e526
          have b5e627 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e527 (σ X0)
               grind)
            | exact superpose b5e527 b5e19
            | exact resolve b5e19 b5e527
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e635 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e627 X0
               have i₂ := b5e527 X0
               grind)
            | exact superpose b5e527 b5e627
            | exact resolve b5e627 b5e527
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e527 b5e627
          have b5e849 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e635 y
               grind)
            | exact superpose b5e635 b5e24
            | exact resolve b5e24 b5e635
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e635
          have b5e875 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e849
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e849
            | exact resolve b5e849 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e849
          have b5e876 : False := by grind
          exact b5e876
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e63 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e82 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b6e84 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b6e82 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e82
        have b6e447 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e84 X0
             have i₂ := b6e63 X0 X1
             grind)
          | (have i₁ := b6e84 X0
             have i₂ := b6e63 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e63 b6e84
          | (have j1 := b6e63 X1 X0
             grind)
          | exact resolve b6e84 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63 b6e84
        have b6e471 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e447 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e447
        have b6e1308 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e471 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e471
        have b6e1309 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e1308 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1308
        have b6e1379 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e1309 (σ X0)
             grind)
          | exact superpose b6e1309 b6e18
          | exact resolve b6e18 b6e1309
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1386 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e1379 X0
             have i₂ := b6e1309 X0
             grind)
          | exact superpose b6e1309 b6e1379
          | exact resolve b6e1379 b6e1309
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1309 b6e1379
        have b6e2171 : (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e1386 x
             grind)
          | exact superpose b6e1386 b6e22
          | exact resolve b6e22 b6e1386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1386
        have b6e2529 : (M.op x x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (M.op x x)
             have i₂ := b6e2171
             grind)
          | exact superpose b6e2171 b6e13
          | exact resolve b6e13 b6e2171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2171
        have b6e2548 : y = (M.op x x) := by
          first
          | (have i₁ := b6e2529
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e2529
          | exact resolve b6e2529 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2529
        have b6e2553 : False := by grind
        exact b6e2553
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e70 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e90 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b7e92 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b7e90 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e472 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e92 X0
               have i₂ := b7e70 X0 X1
               grind)
            | (have i₁ := b7e92 X0
               have i₂ := b7e70 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e70 b7e92
            | (have j1 := b7e70 X1 X0
               grind)
            | exact resolve b7e92 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70 b7e92
          have b7e502 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e472 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e472
          have b7e874 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e502 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e502
          have b7e875 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e874 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e874
          have b7e962 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e875 (σ X0)
               grind)
            | exact superpose b7e875 b7e19
            | exact resolve b7e19 b7e875
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e969 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e962 X0
               have i₂ := b7e875 X0
               grind)
            | exact superpose b7e875 b7e962
            | exact resolve b7e962 b7e875
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e875 b7e962
          have b7e1397 : (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e969 y
               grind)
            | exact superpose b7e969 b7e24
            | exact resolve b7e24 b7e969
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e969
          have b7e2083 : (M.op y y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e1397
               grind)
            | exact superpose b7e1397 b7e14
            | exact resolve b7e14 b7e1397
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1397
          have b7e2102 : x = (M.op y y) := by
            first
            | (have i₁ := b7e2083
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e2083
            | exact resolve b7e2083 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2083
          have b7e2107 : False := by grind
          exact b7e2107
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b8e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ y) (σ x)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e284 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e65 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e285 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e284
               have r₂ := b8e24
               grind)
            | exact resolve b8e284 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e284
          have b8e286 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e285
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e285
            | exact resolve b8e285 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e285
          have b8e287 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e286
               grind)
            | exact superpose b8e286 b8e20
            | exact resolve b8e20 b8e286
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e286
          have b8e297 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e287
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e287
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e287 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e287
          have b8e298 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e297
          have b8e299 : x = (M.op y y) := by
            first
            | (have r₁ := b8e298
               have r₂ := b8e21
               grind)
            | exact resolve b8e298 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e298
          have b8e301 : False := by grind
          exact b8e301

/-- `Equation1845`: `x = (x ◇ (x ◇ y)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyy_y_pxx_pxx_pxy_Equation1845 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1845 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1845.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
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
      have b0e41 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
      have b0e45 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e43
      have b0e46 : (M.op x x) = (k x y) := by grind
      clear b0e41
      have b0e47 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e45
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e45
        | exact resolve b0e45 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e48 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e47
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e47
        | exact resolve b0e47 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e47
      have b0e49 : False := by grind
      exact b0e49
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op x x) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
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
        have b1e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 (τ X0) X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e18
          | exact resolve b1e18 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e18
          | exact resolve b1e18 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k (τ X0) X1)
             have i₂ := b1e24 X0 X1
             grind)
          | exact superpose b1e24 b1e13
          | exact resolve b1e13 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24
        have b1e32 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 (M.op X0 X1)) X0) (M.op X3 X3)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e12 (M.op X0 (M.op X0 X1)) (M.op x x) X3
             have i₂ := b1e12 X0 X1 x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
             have i₂ := b1e12 X0 X1 (M.op X0 (M.op X0 X1))
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (σ y)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e44 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e18 (k X0 (τ X1)) X2
             have i₂ := b1e25 X1 X0
             grind)
          | exact superpose b1e25 b1e18
          | exact resolve b1e18 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e45 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e25 X1 X0
             grind)
          | exact superpose b1e25 b1e13
          | exact resolve b1e13 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e48 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b1e49 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e51 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) ≠ X0 ∨ (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = (k (M.op X0 (M.op X0 X1)) (M.op X2 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e15 (M.op X0 (M.op X0 X1)) (M.op X2 X2)
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e15
          | (have j0 := b1e15 (M.op X0 (M.op X0 X1)) (M.op X2 X2)
             grind)
          | exact resolve b1e15 b1e12
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
        have b1e54 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b1e49
        have b1e55 : (M.op x x) = (k x y) := by grind
        clear b1e48
        have b1e57 : (σ y) = (σ (k y y)) := by
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
        have b1e59 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e57
             have i₂ := b1e53 y
             grind)
          | exact superpose b1e53 b1e57
          | exact resolve b1e57 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57
        have b1e61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
          | (have i₁ := b1e61 X0
             have i₂ := b1e53 X0
             grind)
          | exact superpose b1e53 b1e61
          | exact resolve b1e61 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e70 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 X0 (σ y)
             grind)
          | (have r₁ := b1e16 X0 (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e71 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e70 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70
        have b1e72 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e71 X0
             have j1 := b1e15 X0 (σ y)
             grind)
          | (have r₁ := b1e71 (σ y)
             have r₂ := b1e15 (σ y) (σ y)
             grind)
          | (have r₁ := b1e71 X0
             have r₂ := b1e15 X0 (σ y)
             grind)
          | exact resolve b1e71 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71
        have b1e97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b1e106 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e97 X0 X1
             have i₂ := b1e66 X0
             grind)
          | exact superpose b1e66 b1e97
          | (have j0 := b1e97 X0 X1
             grind)
          | exact resolve b1e97 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e97
        have b1e114 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e106 X0 X1
             have i₂ := b1e66 X1
             grind)
          | exact superpose b1e66 b1e106
          | (have j0 := b1e106 X0 X1
             grind)
          | exact resolve b1e106 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e106
        have b1e121 : (M.op y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (M.op y y)
             have i₂ := b1e59
             grind)
          | exact superpose b1e59 b1e13
          | exact resolve b1e13 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e122 : y = (M.op y y) := by
          first
          | (have i₁ := b1e121
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e121
          | exact resolve b1e121 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e121
        have b1e129 : ∀ X0 : G, (k X0 (σ y)) ≠ (k X0 (σ y)) ∨ (k X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 X0
             have i₂ := b1e72 X0
             grind)
          | exact superpose b1e72 b1e15
          | exact resolve b1e15 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e138 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 y
             have i₂ := b1e72 (σ X0)
             grind)
          | exact superpose b1e72 b1e18
          | exact resolve b1e18 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e141 : ∀ X0 : G, (k X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e129 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e129
        have b1e148 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 y
             have i₂ := b1e122
             grind)
          | exact superpose b1e122 b1e16
          | (have j0 := b1e16 X0 y
             grind)
          | (have r₁ := b1e16 X0 y
             have r₂ := b1e122
             grind)
          | exact resolve b1e16 b1e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e150 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e148 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e148
        have b1e152 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e150 X0
             have j1 := b1e15 X0 y
             grind)
          | (have r₁ := b1e150 y
             have r₂ := b1e15 y y
             grind)
          | (have r₁ := b1e150 X0
             have r₂ := b1e15 X0 y
             grind)
          | exact resolve b1e150 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e150
        have b1e165 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e34 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))
             have i₂ := b1e12 X0 X1 (M.op X0 (M.op X0 X1))
             grind)
          | exact superpose b1e12 b1e34
          | exact resolve b1e34 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e184 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X3)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e33 (M.op X0 (M.op X0 X1)) (M.op x x) X3
             have i₂ := b1e12 X0 X1 x
             grind)
          | exact superpose b1e12 b1e33
          | exact resolve b1e33 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e191 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X3 X3)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e33 X0 x X3
             have i₂ := b1e33 X0 x X1
             grind)
          | (have i₁ := b1e33 x x x
             have i₂ := b1e33 x X1 x
             grind)
          | exact superpose b1e33 b1e33
          | exact resolve b1e33 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e195 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X1 (k X0 (σ y))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e33 X1 X2 X0
             have i₂ := b1e72 X0
             grind)
          | exact superpose b1e72 b1e33
          | exact resolve b1e33 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e199 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e33 X0 X1 y
             have i₂ := b1e122
             grind)
          | exact superpose b1e122 b1e33
          | exact resolve b1e33 b1e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e206 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X3 X3)) = X0 := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e12 X0 x X3
             have i₂ := b1e33 X0 x X1
             grind)
          | (have i₁ := b1e12 x x x
             have i₂ := b1e33 x X1 x
             grind)
          | exact superpose b1e33 b1e12
          | exact resolve b1e12 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e228 : ∀ X0 X1 : G, (M.op X1 (k X0 (σ y))) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e195 X0 X1 x
             have i₂ := b1e165 X1 x
             grind)
          | exact superpose b1e165 b1e195
          | exact resolve b1e195 b1e165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e195
        have b1e234 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e184 X0 X1 x
             have i₂ := b1e12 X0 X1 x
             grind)
          | exact superpose b1e12 b1e184
          | exact resolve b1e184 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e184
        have b1e236 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e234 X0 x
             have i₂ := b1e165 X0 x
             grind)
          | exact superpose b1e165 b1e234
          | exact resolve b1e234 b1e165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e234
        have b1e268 : ∀ X0 : G, (k X0 y) ≠ (k X0 y) ∨ (k X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 X0
             have i₂ := b1e152 X0
             grind)
          | exact superpose b1e152 b1e15
          | exact resolve b1e15 b1e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e277 : ∀ X0 : G, (k X0 (σ y)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b1e72 X0
             have i₂ := b1e152 X0
             grind)
          | exact superpose b1e152 b1e72
          | exact resolve b1e72 b1e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e282 : ∀ X0 : G, (k X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e268 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e268
        have b1e293 : ∀ X0 X1 : G, (M.op X0 (k X0 (σ y))) = (M.op (M.op (M.op X0 (k X0 (σ y))) X0) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e32 X0 X0 x
             have i₂ := b1e72 X0
             grind)
          | exact superpose b1e72 b1e32
          | exact resolve b1e32 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e319 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 (M.op X0 X1)) X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b1e32 X0 X1 y
             have i₂ := b1e122
             grind)
          | exact superpose b1e122 b1e32
          | exact resolve b1e32 b1e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32 b1e122
        have b1e342 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) X0) y) := by
          intro X0
          first
          | (have i₁ := b1e319 X0 x
             have i₂ := b1e165 X0 x
             grind)
          | exact superpose b1e165 b1e319
          | exact resolve b1e319 b1e165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e319
        have b1e357 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) X0) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e293 X0 X1
             have i₂ := b1e228 X0 X0
             grind)
          | exact superpose b1e228 b1e293
          | exact resolve b1e293 b1e228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e293
        have b1e368 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e342 X0
             have i₂ := b1e236 X0
             grind)
          | exact superpose b1e236 b1e342
          | exact resolve b1e342 b1e236
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e342
        have b1e381 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e357 X0 X1
             have i₂ := b1e236 X0
             grind)
          | exact superpose b1e236 b1e357
          | exact resolve b1e357 b1e236
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e357
        have b1e386 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e381 X0 X1
             have i₂ := b1e368 X0
             grind)
          | exact superpose b1e368 b1e381
          | exact resolve b1e381 b1e368
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e381
        have b1e596 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) y) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e282 (σ X0)
             grind)
          | exact superpose b1e282 b1e18
          | exact resolve b1e18 b1e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e609 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) y) := by
          intro X0
          first
          | (have i₁ := b1e596 X0
             have i₂ := b1e53 X0
             grind)
          | exact superpose b1e53 b1e596
          | exact resolve b1e596 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e596
        have b1e1341 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 y
             have i₂ := b1e141 (σ X0)
             grind)
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e141 (σ X0)
             grind)
          | exact superpose b1e141 b1e18
          | exact resolve b1e18 b1e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e141
        have b1e1344 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e1341 X0
             have i₂ := b1e18 X0 X0
             grind)
          | exact superpose b1e18 b1e1341
          | exact resolve b1e1341 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1341
        have b1e1352 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e1344 X0
             have i₂ := b1e53 X0
             grind)
          | exact superpose b1e53 b1e1344
          | exact resolve b1e1344 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1344
        have b1e1999 : ∀ X0 : G, (M.op (M.op X0 y) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e236 X0
             have i₂ := b1e368 X0
             grind)
          | exact superpose b1e368 b1e236
          | exact resolve b1e236 b1e368
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e236
        have b1e2036 : (σ (M.op x x)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e368 (σ x)
             grind)
          | exact superpose b1e368 b1e23
          | exact resolve b1e23 b1e368
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2144 : x = (M.op (M.op x x) x) := by
          first
          | (have i₁ := b1e1999 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1999
          | exact resolve b1e1999 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2149 : ∀ X0 X1 : G, (M.op (M.op X0 y) X0) = (M.op (M.op X0 y) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e33 (M.op X0 y) X0 X1
             have i₂ := b1e1999 X0
             grind)
          | exact superpose b1e1999 b1e33
          | exact resolve b1e33 b1e1999
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2162 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op (M.op X0 y) X0) := by
          intro X0
          first
          | (have i₁ := b1e2149 X0 x
             have i₂ := b1e386 (M.op X0 y) x
             grind)
          | exact superpose b1e386 b1e2149
          | exact resolve b1e2149 b1e386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2149
        have b1e2169 : ∀ X0 : G, (M.op (M.op X0 y) y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e2162 X0
             have i₂ := b1e1999 X0
             grind)
          | exact superpose b1e1999 b1e2162
          | exact resolve b1e2162 b1e1999
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1999 b1e2162
        have b1e2274 : ∀ X0 : G, (M.op (M.op x x) x) = (M.op (M.op x x) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e33 (M.op x x) x X0
             have i₂ := b1e2144
             grind)
          | exact superpose b1e2144 b1e33
          | exact resolve b1e33 b1e2144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e2287 : (M.op (M.op x x) x) = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b1e2274 x
             have i₂ := b1e386 (M.op x x) x
             grind)
          | exact superpose b1e386 b1e2274
          | exact resolve b1e2274 b1e386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2274
        have b1e2292 : x = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b1e2287
             have i₂ := b1e2144
             grind)
          | exact superpose b1e2144 b1e2287
          | exact resolve b1e2287 b1e2144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2287
        have b1e2457 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e114 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e114
        have b1e3342 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) y) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 y
             have i₂ := b1e277 (σ X0)
             grind)
          | exact superpose b1e277 b1e18
          | exact resolve b1e18 b1e277
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e3736 : ∀ X0 : G, (M.op x x) ≠ (M.op (M.op (M.op x x) x) (M.op (M.op x x) x)) ∨ (k (M.op (M.op x x) x) (M.op X0 X0)) = (M.op (M.op (M.op x x) x) (M.op (M.op x x) x)) := by
          intro X0
          first
          | (have i₁ := b1e51 (M.op x x) y x
             have i₂ := b1e2292
             grind)
          | exact superpose b1e2292 b1e51
          | exact resolve b1e51 b1e2292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e3803 : ∀ X0 : G, (M.op x x) ≠ (k (M.op (M.op x x) x) (σ y)) ∨ (k (M.op (M.op x x) x) (M.op X0 X0)) = (M.op (M.op (M.op x x) x) (M.op (M.op x x) x)) := by
          intro X0
          first
          | (have i₁ := b1e3736 X0
             have i₂ := b1e72 (M.op (M.op x x) x)
             grind)
          | exact superpose b1e72 b1e3736
          | (have j0 := b1e3736 X0
             grind)
          | exact resolve b1e3736 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3736
        have b1e3840 : ∀ X0 : G, (M.op x x) ≠ (k (M.op (M.op x x) x) y) ∨ (k (M.op (M.op x x) x) (M.op X0 X0)) = (M.op (M.op (M.op x x) x) (M.op (M.op x x) x)) := by
          intro X0
          first
          | (have i₁ := b1e3803 X0
             have i₂ := b1e277 (M.op (M.op x x) x)
             grind)
          | exact superpose b1e277 b1e3803
          | (have j0 := b1e3803 X0
             grind)
          | exact resolve b1e3803 b1e277
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3803
        have b1e3875 : ∀ X0 : G, (M.op x x) ≠ (k x y) ∨ (k (M.op (M.op x x) x) (M.op X0 X0)) = (M.op (M.op (M.op x x) x) (M.op (M.op x x) x)) := by
          intro X0
          first
          | (have i₁ := b1e3840 X0
             have i₂ := b1e2144
             grind)
          | exact superpose b1e2144 b1e3840
          | (have j0 := b1e3840 X0
             grind)
          | exact resolve b1e3840 b1e2144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3840
        have b1e3910 : ∀ X0 : G, (k (M.op (M.op x x) x) (M.op X0 X0)) = (M.op (M.op (M.op x x) x) (M.op (M.op x x) x)) := by
          intro X0
          first
          | (have j0 := b1e3875 X0
             grind)
          | (have r₁ := b1e3875 X0
             have r₂ := b1e55
             grind)
          | exact resolve b1e3875 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3875
        have b1e3941 : ∀ X0 : G, (k (M.op (M.op x x) x) (M.op X0 X0)) = (k (M.op (M.op x x) x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e3910 X0
             have i₂ := b1e72 (M.op (M.op x x) x)
             grind)
          | exact superpose b1e72 b1e3910
          | exact resolve b1e3910 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3910
        have b1e3966 : ∀ X0 : G, (k (M.op (M.op x x) x) (M.op X0 X0)) = (k (M.op (M.op x x) x) y) := by
          intro X0
          first
          | (have i₁ := b1e3941 X0
             have i₂ := b1e277 (M.op (M.op x x) x)
             grind)
          | exact superpose b1e277 b1e3941
          | exact resolve b1e3941 b1e277
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3941
        have b1e3986 : ∀ X0 : G, (k x y) = (k x (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e3966 X0
             have i₂ := b1e2144
             grind)
          | exact superpose b1e2144 b1e3966
          | exact resolve b1e3966 b1e2144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2144 b1e3966
        have b1e3999 : ∀ X0 : G, (M.op x x) = (k x (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e3986 X0
             have i₂ := b1e152 x
             grind)
          | exact superpose b1e152 b1e3986
          | exact resolve b1e3986 b1e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3986
        have b1e4031 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (M.op (M.op X0 X0) y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e386 X1 (M.op X0 X0)
             have i₂ := b1e386 (M.op X0 X0) X0
             grind)
          | exact superpose b1e386 b1e386
          | exact resolve b1e386 b1e386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e4108 : ∀ X0 : G, (k (M.op X0 X0) y) = (M.op (M.op X0 X0) y) := by
          intro X0
          first
          | (have i₁ := b1e152 (M.op X0 X0)
             have i₂ := b1e386 (M.op X0 X0) X0
             grind)
          | exact superpose b1e386 b1e152
          | exact resolve b1e152 b1e386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e4228 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e29 X0 y
             have i₂ := b1e277 X0
             grind)
          | exact superpose b1e277 b1e29
          | exact resolve b1e29 b1e277
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e4230 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e29 X0 y
             have i₂ := b1e72 X0
             grind)
          | exact superpose b1e72 b1e29
          | exact resolve b1e29 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e4232 : ∀ X0 : G, (k (τ (σ X0)) X0) = (τ (k (σ X0) y)) := by
          intro X0
          first
          | (have i₁ := b1e29 (σ X0) X0
             have i₂ := b1e282 (σ X0)
             grind)
          | exact superpose b1e282 b1e29
          | exact resolve b1e29 b1e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e4258 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k X0 (τ y)) := by
          intro X0
          first
          | (have i₁ := b1e4232 X0
             have i₂ := b1e45 X0 y
             grind)
          | exact superpose b1e45 b1e4232
          | exact resolve b1e4232 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4232
        have b1e4267 : ∀ X0 : G, (k X0 X0) = (k X0 (τ y)) := by
          intro X0
          first
          | (have i₁ := b1e4258 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e4258
          | exact resolve b1e4258 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4258
        have b1e4291 : ∀ X0 : G, (k X0 y) = (k X0 (τ y)) := by
          intro X0
          first
          | (have i₁ := b1e282 X0
             have i₂ := b1e4267 X0
             grind)
          | (have i₁ := b1e282 (τ y)
             have i₂ := b1e4267 (τ y)
             grind)
          | exact superpose b1e4267 b1e282
          | exact resolve b1e282 b1e4267
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e282
        have b1e4299 : ∀ X0 : G, (k (τ (σ X0)) X0) = (τ (k (σ X0) (τ y))) := by
          intro X0
          first
          | (have i₁ := b1e29 (σ X0) X0
             have i₂ := b1e4267 (σ X0)
             grind)
          | exact superpose b1e4267 b1e29
          | exact resolve b1e29 b1e4267
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4267
        have b1e4336 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k X0 (τ (τ y))) := by
          intro X0
          first
          | (have i₁ := b1e4299 X0
             have i₂ := b1e45 X0 (τ y)
             grind)
          | exact superpose b1e45 b1e4299
          | exact resolve b1e4299 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4299
        have b1e4357 : ∀ X0 : G, (k X0 X0) = (k X0 (τ (τ y))) := by
          intro X0
          first
          | (have i₁ := b1e4336 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e4336
          | exact resolve b1e4336 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4336
        have b1e4486 : ∀ X0 : G, (τ (k (σ X0) y)) = (k X0 (τ (τ y))) := by
          intro X0
          first
          | (have i₁ := b1e45 X0 (τ y)
             have i₂ := b1e4291 (σ X0)
             grind)
          | exact superpose b1e4291 b1e45
          | exact resolve b1e45 b1e4291
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4291
        have b1e4489 : ∀ X0 : G, (k (τ (σ X0)) y) = (k X0 (τ (τ y))) := by
          intro X0
          first
          | (have i₁ := b1e4486 X0
             have i₂ := b1e4228 (σ X0)
             grind)
          | exact superpose b1e4228 b1e4486
          | exact resolve b1e4486 b1e4228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4486
        have b1e4501 : ∀ X0 : G, (k X0 y) = (k X0 (τ (τ y))) := by
          intro X0
          first
          | (have i₁ := b1e4489 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e4489
          | exact resolve b1e4489 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4489
        have b1e4572 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ (M.op X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e386 X1 (σ X0)
             have i₂ := b1e66 X0
             grind)
          | exact superpose b1e66 b1e386
          | exact resolve b1e386 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e5246 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ (k X0 y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e386 X1 (σ X0)
             have i₂ := b1e138 X0
             grind)
          | exact superpose b1e138 b1e386
          | exact resolve b1e386 b1e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e8116 : ∀ X0 : G, (M.op (k X0 (σ y)) (σ y)) = (k (k X0 (σ y)) y) := by
          intro X0
          first
          | (have i₁ := b1e152 (k X0 (σ y))
             have i₂ := b1e228 X0 (k X0 (σ y))
             grind)
          | exact superpose b1e228 b1e152
          | exact resolve b1e152 b1e228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e8125 : ∀ X0 : G, (σ (M.op (k X0 (σ y)) (σ y))) = (σ (k (k X0 (σ y)) y)) := by
          intro X0
          first
          | (have i₁ := b1e1352 (k X0 (σ y))
             have i₂ := b1e228 X0 (k X0 (σ y))
             grind)
          | exact superpose b1e228 b1e1352
          | exact resolve b1e1352 b1e228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e228
        have b1e8177 : ∀ X0 : G, (σ (k (k X0 y) y)) = (σ (M.op (k X0 y) (σ y))) := by
          intro X0
          first
          | (have i₁ := b1e8125 X0
             have i₂ := b1e277 X0
             grind)
          | exact superpose b1e277 b1e8125
          | exact resolve b1e8125 b1e277
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8125
        have b1e8186 : ∀ X0 : G, (k (k X0 y) y) = (M.op (k X0 y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e8116 X0
             have i₂ := b1e277 X0
             grind)
          | exact superpose b1e277 b1e8116
          | exact resolve b1e8116 b1e277
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8116
        have b1e8240 : ∀ X0 : G, (σ (k (k X0 y) y)) = (σ (M.op (k X0 y) y)) := by
          intro X0
          first
          | (have i₁ := b1e8177 X0
             have i₂ := b1e368 (k X0 y)
             grind)
          | exact superpose b1e368 b1e8177
          | exact resolve b1e8177 b1e368
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8177
        have b1e8249 : ∀ X0 : G, (M.op (k X0 y) y) = (k (k X0 y) y) := by
          intro X0
          first
          | (have i₁ := b1e8186 X0
             have i₂ := b1e368 (k X0 y)
             grind)
          | exact superpose b1e368 b1e8186
          | exact resolve b1e8186 b1e368
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e368 b1e8186
        have b1e11540 : ∀ X0 X1 : G, (k (k (σ X0) X1) y) = (σ (k (k X0 (τ X1)) y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e277 (k (σ X0) X1)
             have i₂ := b1e44 X0 X1 y
             grind)
          | exact superpose b1e44 b1e277
          | exact resolve b1e277 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e277
        have b1e12689 : ∀ X0 : G, (σ (k (M.op X0 X0) y)) = (M.op (k (σ X0) y) (k (σ X0) y)) := by
          intro X0
          first
          | (have i₁ := b1e138 (M.op X0 X0)
             have i₂ := b1e609 X0
             grind)
          | exact superpose b1e609 b1e138
          | exact resolve b1e138 b1e609
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e12709 : ∀ X0 : G, (σ (k (M.op X0 X0) y)) = (k (k (σ X0) y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e12689 X0
             have i₂ := b1e72 (k (σ X0) y)
             grind)
          | exact superpose b1e72 b1e12689
          | exact resolve b1e12689 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72 b1e12689
        have b1e12760 : ∀ X0 : G, (σ (k (M.op X0 X0) y)) = (σ (k (k X0 (τ y)) y)) := by
          intro X0
          first
          | (have i₁ := b1e12709 X0
             have i₂ := b1e44 X0 y y
             grind)
          | exact superpose b1e44 b1e12709
          | exact resolve b1e12709 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44 b1e12709
        have b1e12796 : ∀ X0 : G, (σ (k (M.op X0 X0) y)) = (k (k (σ X0) y) y) := by
          intro X0
          first
          | (have i₁ := b1e12760 X0
             have i₂ := b1e11540 X0 y
             grind)
          | exact superpose b1e11540 b1e12760
          | exact resolve b1e12760 b1e11540
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11540 b1e12760
        have b1e12811 : ∀ X0 : G, (σ (k (M.op X0 X0) y)) = (M.op (k (σ X0) y) y) := by
          intro X0
          first
          | (have i₁ := b1e12796 X0
             have i₂ := b1e8249 (σ X0)
             grind)
          | exact superpose b1e8249 b1e12796
          | exact resolve b1e12796 b1e8249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8249 b1e12796
        have b1e12821 : ∀ X0 : G, (σ (k (M.op X0 X0) y)) = (M.op (σ (k X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b1e12811 X0
             have i₂ := b1e3342 X0
             grind)
          | exact superpose b1e3342 b1e12811
          | exact resolve b1e12811 b1e3342
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12811
        have b1e12829 : ∀ X0 : G, (σ (M.op (M.op X0 X0) y)) = (M.op (σ (k X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b1e12821 X0
             have i₂ := b1e4108 X0
             grind)
          | exact superpose b1e4108 b1e12821
          | exact resolve b1e12821 b1e4108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12821
        have b1e12892 : ∀ X0 : G, (k (σ (M.op X0 X0)) y) = (σ (k (k X0 y) y)) := by
          intro X0
          first
          | (have i₁ := b1e3342 (k X0 y)
             have i₂ := b1e1352 X0
             grind)
          | exact superpose b1e1352 b1e3342
          | exact resolve b1e3342 b1e1352
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1352
        have b1e12938 : ∀ X0 : G, (k (σ (M.op X0 X0)) y) = (σ (M.op (k X0 y) y)) := by
          intro X0
          first
          | (have i₁ := b1e12892 X0
             have i₂ := b1e8240 X0
             grind)
          | exact superpose b1e8240 b1e12892
          | exact resolve b1e12892 b1e8240
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12892
        have b1e12946 : ∀ X0 : G, (σ (k (M.op X0 X0) y)) = (σ (M.op (k X0 y) y)) := by
          intro X0
          first
          | (have i₁ := b1e12938 X0
             have i₂ := b1e3342 (M.op X0 X0)
             grind)
          | exact superpose b1e3342 b1e12938
          | exact resolve b1e12938 b1e3342
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12938
        have b1e12952 : ∀ X0 : G, (σ (M.op (M.op X0 X0) y)) = (σ (M.op (k X0 y) y)) := by
          intro X0
          first
          | (have i₁ := b1e12946 X0
             have i₂ := b1e4108 X0
             grind)
          | exact superpose b1e4108 b1e12946
          | exact resolve b1e12946 b1e4108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12946
        have b1e12955 : ∀ X0 : G, (M.op (σ (k X0 y)) y) = (σ (M.op (k X0 y) y)) := by
          intro X0
          first
          | (have i₁ := b1e12952 X0
             have i₂ := b1e12829 X0
             grind)
          | exact superpose b1e12829 b1e12952
          | exact resolve b1e12952 b1e12829
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12829 b1e12952
        have b1e16972 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k X0 (τ (τ (τ y)))) := by
          intro X0
          first
          | (have i₁ := b1e45 X0 (τ (τ y))
             have i₂ := b1e4357 (σ X0)
             grind)
          | (have i₁ := b1e45 X0 (σ X0)
             have i₂ := b1e4357 (σ X0)
             grind)
          | exact superpose b1e4357 b1e45
          | exact resolve b1e45 b1e4357
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4357
        have b1e16979 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k X0 (τ (τ (τ y)))) := by
          intro X0
          first
          | (have i₁ := b1e16972 X0
             have i₂ := b1e29 (σ X0) X0
             grind)
          | exact superpose b1e29 b1e16972
          | exact resolve b1e16972 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29 b1e16972
        have b1e17031 : ∀ X0 : G, (k X0 X0) = (k X0 (τ (τ (τ y)))) := by
          intro X0
          first
          | (have i₁ := b1e16979 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e16979
          | exact resolve b1e16979 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e16979
        have b1e20240 : ∀ X0 : G, (M.op x x) = (k x (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e3999 X0
             have i₂ := b1e152 X0
             grind)
          | exact superpose b1e152 b1e3999
          | exact resolve b1e3999 b1e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3999
        have b1e21087 : ∀ X0 : G, (τ (k (σ X0) y)) = (k X0 (τ (τ (τ y)))) := by
          intro X0
          first
          | (have i₁ := b1e45 X0 (τ (τ y))
             have i₂ := b1e4501 (σ X0)
             grind)
          | exact superpose b1e4501 b1e45
          | exact resolve b1e45 b1e4501
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45 b1e4501
        have b1e21090 : ∀ X0 : G, (k (τ (σ X0)) y) = (k X0 (τ (τ (τ y)))) := by
          intro X0
          first
          | (have i₁ := b1e21087 X0
             have i₂ := b1e4228 (σ X0)
             grind)
          | exact superpose b1e4228 b1e21087
          | exact resolve b1e21087 b1e4228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4228 b1e21087
        have b1e21112 : ∀ X0 : G, (k X0 y) = (k X0 (τ (τ (τ y)))) := by
          intro X0
          first
          | (have i₁ := b1e21090 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e21090
          | exact resolve b1e21090 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e21090
        have b1e60211 : ∀ X0 : G, (M.op X0 X0) = (k X0 (τ (τ (τ y)))) := by
          intro X0
          first
          | (have i₁ := b1e53 X0
             have i₂ := b1e17031 X0
             grind)
          | (have i₁ := b1e53 (τ (τ (τ y)))
             have i₂ := b1e17031 (τ (τ (τ y)))
             grind)
          | exact superpose b1e17031 b1e53
          | exact resolve b1e53 b1e17031
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53 b1e17031
        have b1e80025 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e4031 (M.op X0 X0) X2
             have i₂ := b1e191 (M.op X0 X0) X0 X1
             grind)
          | (have i₁ := b1e4031 (M.op X0 X0) X2
             have i₂ := b1e191 (M.op X0 X0) X1 X0
             grind)
          | exact superpose b1e191 b1e4031
          | exact resolve b1e4031 b1e191
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e191
        have b1e80077 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b1e4031 x X0
             have i₂ := b1e2292
             grind)
          | exact superpose b1e2292 b1e4031
          | exact resolve b1e4031 b1e2292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e80245 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) y) y) = (k (M.op (M.op X0 X0) y) y) := by
          intro X0
          first
          | (have i₁ := b1e152 (M.op (M.op X0 X0) y)
             have i₂ := b1e4031 X0 (M.op (M.op X0 X0) y)
             grind)
          | exact superpose b1e4031 b1e152
          | exact resolve b1e152 b1e4031
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e152
        have b1e80256 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op X0 X0) y) y)) (M.op X2 X2)) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e206 X1 (M.op (M.op X0 X0) y) X2
             have i₂ := b1e4031 X0 (M.op (M.op X0 X0) y)
             grind)
          | exact superpose b1e4031 b1e206
          | exact resolve b1e206 b1e4031
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e206
        have b1e80349 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) y) y) = (k (M.op (M.op X0 X0) y) (τ (τ (τ y)))) := by
          intro X0
          first
          | (have i₁ := b1e60211 (M.op (M.op X0 X0) y)
             have i₂ := b1e4031 X0 (M.op (M.op X0 X0) y)
             grind)
          | exact superpose b1e4031 b1e60211
          | exact resolve b1e60211 b1e4031
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4031 b1e60211
        have b1e80485 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) y) y) = (k (M.op (M.op X0 X0) y) y) := by
          intro X0
          first
          | (have i₁ := b1e80349 X0
             have i₂ := b1e21112 (M.op (M.op X0 X0) y)
             grind)
          | exact superpose b1e21112 b1e80349
          | exact resolve b1e80349 b1e21112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e21112 b1e80349
        have b1e80548 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op (M.op X0 X0) y) y)) y) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e80256 X0 X1 x
             have i₂ := b1e386 (M.op X1 (M.op (M.op (M.op X0 X0) y) y)) x
             grind)
          | exact superpose b1e386 b1e80256
          | exact resolve b1e80256 b1e386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80256
        have b1e80556 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) y) y) := by
          intro X0
          first
          | (have i₁ := b1e80245 X0
             have i₂ := b1e2169 (M.op X0 X0)
             grind)
          | exact superpose b1e2169 b1e80245
          | exact resolve b1e80245 b1e2169
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80245
        have b1e80655 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) x)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e80025 X0 X1 X2
             have i₂ := b1e80077 (M.op (M.op X0 X0) (M.op X1 X1))
             grind)
          | exact superpose b1e80077 b1e80025
          | exact resolve b1e80025 b1e80077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80025
        have b1e80729 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) y) = (k (M.op (M.op X0 X0) x) y) := by
          intro X0
          first
          | (have i₁ := b1e80485 X0
             have i₂ := b1e80077 (M.op X0 X0)
             grind)
          | exact superpose b1e80077 b1e80485
          | exact resolve b1e80485 b1e80077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80485
        have b1e80765 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op (M.op X0 X0) y) y)) x) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e80548 X0 X1
             have i₂ := b1e80077 (M.op X1 (M.op (M.op (M.op X0 X0) y) y))
             grind)
          | exact superpose b1e80077 b1e80548
          | exact resolve b1e80548 b1e80077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80548
        have b1e80767 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) x) y) := by
          intro X0
          first
          | (have i₁ := b1e80556 X0
             have i₂ := b1e80077 (M.op X0 X0)
             grind)
          | exact superpose b1e80077 b1e80556
          | exact resolve b1e80556 b1e80077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80556
        have b1e80822 : ∀ X0 X2 : G, (M.op X2 y) = (M.op X2 (M.op (M.op (M.op X0 X0) y) x)) := by
          intro X0 X2
          first
          | (have i₁ := b1e80655 X0 x X2
             have i₂ := b1e386 (M.op X0 X0) x
             grind)
          | exact superpose b1e386 b1e80655
          | exact resolve b1e80655 b1e386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80655
        have b1e80893 : ∀ X0 : G, (k (M.op (M.op X0 X0) x) y) = (M.op (M.op (M.op X0 X0) x) x) := by
          intro X0
          first
          | (have i₁ := b1e80729 X0
             have i₂ := b1e80077 (M.op (M.op X0 X0) x)
             grind)
          | exact superpose b1e80077 b1e80729
          | exact resolve b1e80729 b1e80077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80729
        have b1e80923 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) x) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e80765 X0 X1
             have i₂ := b1e2169 (M.op X0 X0)
             grind)
          | exact superpose b1e2169 b1e80765
          | exact resolve b1e80765 b1e2169
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2169 b1e80765
        have b1e80971 : ∀ X0 X2 : G, (M.op X2 y) = (M.op X2 (M.op (M.op (M.op X0 X0) x) x)) := by
          intro X0 X2
          first
          | (have i₁ := b1e80822 X0 X2
             have i₂ := b1e80077 (M.op X0 X0)
             grind)
          | exact superpose b1e80077 b1e80822
          | exact resolve b1e80822 b1e80077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80822
        have b1e81021 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) x) x) := by
          intro X0
          first
          | (have i₁ := b1e80893 X0
             have i₂ := b1e80767 X0
             grind)
          | exact superpose b1e80767 b1e80893
          | exact resolve b1e80893 b1e80767
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80767 b1e80893
        have b1e81045 : ∀ X1 : G, (M.op (M.op X1 y) x) = X1 := by
          intro X1
          first
          | (have i₁ := b1e80923 x X1
             have i₂ := b1e386 X1 x
             grind)
          | exact superpose b1e386 b1e80923
          | exact resolve b1e80923 b1e386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e386 b1e80923
        have b1e81084 : ∀ X0 X2 : G, (M.op X2 x) = (M.op X2 (M.op (M.op (M.op X0 X0) x) x)) := by
          intro X0 X2
          first
          | (have i₁ := b1e80971 X0 X2
             have i₂ := b1e80077 X2
             grind)
          | exact superpose b1e80077 b1e80971
          | exact resolve b1e80971 b1e80077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80971
        have b1e81123 : ∀ X1 : G, (M.op (M.op X1 x) x) = X1 := by
          intro X1
          first
          | (have i₁ := b1e81045 X1
             have i₂ := b1e80077 X1
             grind)
          | exact superpose b1e80077 b1e81045
          | exact resolve b1e81045 b1e80077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81045
        have b1e81147 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op X2 x) := by
          intro X0 X2
          first
          | (have i₁ := b1e81084 X0 X2
             have i₂ := b1e81021 X0
             grind)
          | exact superpose b1e81021 b1e81084
          | exact resolve b1e81084 b1e81021
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81021 b1e81084
        have b1e81745 : ∀ X0 : G, (M.op (M.op X0 x) X0) = (M.op (M.op X0 x) y) := by
          intro X0
          first
          | (have i₁ := b1e199 (M.op X0 x) x
             have i₂ := b1e81123 X0
             grind)
          | exact superpose b1e81123 b1e199
          | exact resolve b1e199 b1e81123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e199
        have b1e81769 : ∀ X0 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 x) X0) := by
          intro X0
          first
          | (have i₁ := b1e81745 X0
             have i₂ := b1e80077 (M.op X0 x)
             grind)
          | exact superpose b1e80077 b1e81745
          | exact resolve b1e81745 b1e80077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81745
        have b1e81798 : ∀ X0 : G, (M.op (M.op X0 x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e81769 X0
             have i₂ := b1e81123 X0
             grind)
          | (have i₁ := b1e81769 X0
             have i₂ := b1e81123 (M.op (M.op X0 x) x)
             grind)
          | exact superpose b1e81123 b1e81769
          | exact resolve b1e81769 b1e81123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81769
        have b1e83618 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e81798 (M.op X0 x)
             have i₂ := b1e81123 X0
             grind)
          | exact superpose b1e81123 b1e81798
          | exact resolve b1e81798 b1e81123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81123 b1e81798
        have b1e83818 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b1e83618 X0
             have i₂ := b1e165 X0 x
             grind)
          | exact superpose b1e165 b1e83618
          | exact resolve b1e83618 b1e165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e165 b1e83618
        have b1e90834 : (σ (M.op x x)) ≠ (M.op (σ x) x) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e83818 (σ x)
             grind)
          | exact superpose b1e83818 b1e23
          | exact resolve b1e23 b1e83818
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e83818
        have b1e91473 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 y))) = (M.op X1 x) := by
          intro X0 X1
          first
          | (have i₁ := b1e81147 (σ X0) X1
             have i₂ := b1e138 X0
             grind)
          | exact superpose b1e138 b1e81147
          | exact resolve b1e81147 b1e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e138 b1e81147
        have b1e93368 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (σ (M.op (k X0 y) (k X0 y))) ∨ (σ (M.op x x)) = (M.op (σ x) (σ (k X0 y))) := by
          intro X0
          first
          | (have i₁ := b1e2457 x (k X0 y)
             have i₂ := b1e20240 X0
             grind)
          | exact superpose b1e20240 b1e2457
          | (have j0 := b1e2457 x (k X0 y)
             grind)
          | exact resolve b1e2457 b1e20240
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2457 b1e20240
        have b1e93554 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op (k X0 y) (k X0 y))) ∨ (σ (M.op x x)) = (M.op (σ x) (σ (k X0 y))) := by
          intro X0
          first
          | (have j0 := b1e93368 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e93368
        have b1e93679 : ∀ X0 : G, (σ (k X0 y)) = (k (σ (k X0 y)) y) ∨ (σ (M.op x x)) = (M.op (σ x) (σ (k X0 y))) := by
          intro X0
          first
          | (have i₁ := b1e93554 X0
             have i₂ := b1e609 (k X0 y)
             grind)
          | exact superpose b1e609 b1e93554
          | (have j0 := b1e93554 X0
             grind)
          | exact resolve b1e93554 b1e609
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e609 b1e93554
        have b1e93844 : ∀ X0 : G, (σ (k X0 y)) = (σ (k (k X0 y) y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ (k X0 y))) := by
          intro X0
          first
          | (have i₁ := b1e93679 X0
             have i₂ := b1e3342 (k X0 y)
             grind)
          | exact superpose b1e3342 b1e93679
          | (have j0 := b1e93679 X0
             grind)
          | exact resolve b1e93679 b1e3342
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3342 b1e93679
        have b1e93971 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op (k X0 y) y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ (k X0 y))) := by
          intro X0
          first
          | (have i₁ := b1e93844 X0
             have i₂ := b1e8240 X0
             grind)
          | exact superpose b1e8240 b1e93844
          | (have j0 := b1e93844 X0
             grind)
          | exact resolve b1e93844 b1e8240
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8240 b1e93844
        have b1e94085 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ (k X0 y)) y) ∨ (σ (M.op x x)) = (M.op (σ x) (σ (k X0 y))) := by
          intro X0
          first
          | (have i₁ := b1e93971 X0
             have i₂ := b1e12955 X0
             grind)
          | exact superpose b1e12955 b1e93971
          | (have j0 := b1e93971 X0
             grind)
          | exact resolve b1e93971 b1e12955
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12955 b1e93971
        have b1e94180 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ (k X0 y)) x) ∨ (σ (M.op x x)) = (M.op (σ x) (σ (k X0 y))) := by
          intro X0
          first
          | (have i₁ := b1e94085 X0
             have i₂ := b1e80077 (σ (k X0 y))
             grind)
          | exact superpose b1e80077 b1e94085
          | (have j0 := b1e94085 X0
             grind)
          | exact resolve b1e94085 b1e80077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e94085
        have b1e94260 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ x) y) ∨ (σ (k X0 y)) = (M.op (σ (k X0 y)) x) := by
          intro X0
          first
          | (have i₁ := b1e94180 X0
             have i₂ := b1e5246 X0 (σ x)
             grind)
          | exact superpose b1e5246 b1e94180
          | (have j0 := b1e94180 X0
             grind)
          | exact resolve b1e94180 b1e5246
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5246 b1e94180
        have b1e94323 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ (k X0 y)) x) := by
          intro X0
          first
          | (have j0 := b1e94260 X0
             grind)
          | (have r₁ := b1e94260 X0
             have r₂ := b1e2036
             grind)
          | exact resolve b1e94260 b1e2036
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2036 b1e94260
        have b1e127246 : ∀ X0 : G, (k (τ (σ (k X0 y))) y) = (τ (M.op (σ (k X0 y)) x)) := by
          intro X0
          first
          | (have i₁ := b1e4230 (σ (k X0 y))
             have i₂ := b1e91473 X0 (σ (k X0 y))
             grind)
          | exact superpose b1e91473 b1e4230
          | exact resolve b1e4230 b1e91473
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4230 b1e91473
        have b1e127472 : ∀ X0 : G, (τ (σ (k X0 y))) = (k (τ (σ (k X0 y))) y) := by
          intro X0
          first
          | (have i₁ := b1e127246 X0
             have i₂ := b1e94323 X0
             grind)
          | exact superpose b1e94323 b1e127246
          | exact resolve b1e127246 b1e94323
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e94323 b1e127246
        have b1e127678 : ∀ X0 : G, (k X0 y) = (k (k X0 y) y) := by
          intro X0
          first
          | (have i₁ := b1e127472 X0
             have i₂ := b1e13 (k X0 y)
             grind)
          | exact superpose b1e13 b1e127472
          | exact resolve b1e127472 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e127472
        have b1e128942 : (M.op x x) = (k (M.op x x) y) := by
          first
          | (have i₁ := b1e127678 x
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e127678
          | exact resolve b1e127678 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e127678
        have b1e128994 : (M.op x x) = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b1e128942
             have i₂ := b1e4108 x
             grind)
          | exact superpose b1e4108 b1e128942
          | exact resolve b1e128942 b1e4108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4108 b1e128942
        have b1e129020 : x = (M.op x x) := by
          first
          | (have i₁ := b1e128994
             have i₂ := b1e2292
             grind)
          | exact superpose b1e2292 b1e128994
          | exact resolve b1e128994 b1e2292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2292 b1e128994
        have b1e129915 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e4572 x X0
             have i₂ := b1e129020
             grind)
          | exact superpose b1e129020 b1e4572
          | exact resolve b1e4572 b1e129020
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4572 b1e129020
        have b1e129991 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e129915 X0
             have i₂ := b1e80077 X0
             grind)
          | exact superpose b1e80077 b1e129915
          | exact resolve b1e129915 b1e80077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80077 b1e129915
        have b1e174323 : (σ (M.op x x)) = (M.op (σ x) x) := by
          first
          | (have i₁ := b1e66 x
             have i₂ := b1e129991 (σ x)
             grind)
          | exact superpose b1e129991 b1e66
          | exact resolve b1e66 b1e129991
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66 b1e129991
        have b1e174358 : False := by grind
        exact b1e174358
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
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
        have b2e49 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b2e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : (M.op x x) = (k x y) := by grind
        clear b2e49
        have b2e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e51 (σ X0)
             grind)
          | exact superpose b2e51 b2e18
          | exact resolve b2e18 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e54 X0
             have i₂ := b2e51 X0
             grind)
          | exact superpose b2e51 b2e54
          | exact resolve b2e54 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e54
        have b2e90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b2e100 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e90 X0 X1
             have i₂ := b2e61 X0
             grind)
          | exact superpose b2e61 b2e90
          | (have j0 := b2e90 X0 X1
             grind)
          | exact resolve b2e90 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90
        have b2e108 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e100 X0 X1
             have i₂ := b2e61 X1
             grind)
          | exact superpose b2e61 b2e100
          | (have j0 := b2e100 X0 X1
             grind)
          | exact resolve b2e100 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e100
        have b2e279 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e61 y
             grind)
          | exact superpose b2e61 b2e22
          | exact resolve b2e22 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1990 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e108 x y
             grind)
          | exact superpose b2e108 b2e21
          | (have j1 := b2e108 x y
             grind)
          | exact resolve b2e21 b2e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108
        have b2e2051 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have r₁ := b2e1990
             have r₂ := b2e279
             grind)
          | exact resolve b2e1990 b2e279
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e279 b2e1990
        have b2e2089 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e2051
             have r₂ := b2e23
             grind)
          | exact resolve b2e2051 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e2051
        have b2e2105 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e2089
             have i₂ := b2e52
             grind)
          | exact superpose b2e52 b2e2089
          | exact resolve b2e2089 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e2089
        have b2e2115 : False := by grind
        exact b2e2115
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y y) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b3e29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k (τ X0) X1)
             have i₂ := b3e24 X0 X1
             grind)
          | exact superpose b3e24 b3e13
          | exact resolve b3e13 b3e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 (M.op X0 X1)) X0) (M.op X3 X3)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e12 (M.op X0 (M.op X0 X1)) (M.op x x) X3
             have i₂ := b3e12 X0 X1 x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
             have i₂ := b3e12 X0 X1 (M.op X0 (M.op X0 X1))
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) y) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e46 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e33 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))
             have i₂ := b3e12 X0 X1 (M.op X0 (M.op X0 X1))
             grind)
          | exact superpose b3e12 b3e33
          | exact resolve b3e33 b3e12
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
        have b3e67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
          | (have i₁ := b3e67 X0
             have i₂ := b3e57 X0
             grind)
          | exact superpose b3e57 b3e67
          | exact resolve b3e67 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67
        have b3e73 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | (have r₁ := b3e16 X0 y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e74 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e73 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73
        have b3e75 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e74 X0
             have j1 := b3e15 X0 y
             grind)
          | (have r₁ := b3e74 y
             have r₂ := b3e15 y y
             grind)
          | (have r₁ := b3e74 X0
             have r₂ := b3e15 X0 y
             grind)
          | exact resolve b3e74 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74
        have b3e80 : ∀ X0 : G, (k X0 y) ≠ (k X0 y) ∨ (k X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e15 X0 X0
             have i₂ := b3e75 X0
             grind)
          | exact superpose b3e75 b3e15
          | exact resolve b3e15 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e84 : ∀ X0 : G, (k X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e80 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80
        have b3e186 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) y) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e84 (σ X0)
             grind)
          | exact superpose b3e84 b3e18
          | exact resolve b3e18 b3e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e187 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (k (τ X0) y)) := by
          intro X0
          first
          | (have i₁ := b3e24 X0 (τ X0)
             have i₂ := b3e84 (τ X0)
             grind)
          | (have i₁ := b3e24 X0 y
             have i₂ := b3e84 (τ X0)
             grind)
          | exact superpose b3e84 b3e24
          | exact resolve b3e24 b3e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e192 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e187 X0
             have i₂ := b3e24 X0 y
             grind)
          | exact superpose b3e24 b3e187
          | exact resolve b3e187 b3e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24 b3e187
        have b3e193 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) y) := by
          intro X0
          first
          | (have i₁ := b3e186 X0
             have i₂ := b3e57 X0
             grind)
          | exact superpose b3e57 b3e186
          | exact resolve b3e186 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e186
        have b3e196 : ∀ X0 : G, (k X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e192 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e192
          | exact resolve b3e192 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e192
        have b3e244 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X3)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e32 (M.op X0 (M.op X0 X1)) (M.op x x) X3
             have i₂ := b3e12 X0 X1 x
             grind)
          | exact superpose b3e12 b3e32
          | exact resolve b3e32 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e257 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X1 (k X0 y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e32 X1 X2 X0
             have i₂ := b3e75 X0
             grind)
          | exact superpose b3e75 b3e32
          | exact resolve b3e32 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e290 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (k X0 y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e257 X0 X1 x
             have i₂ := b3e46 X1 x
             grind)
          | exact superpose b3e46 b3e257
          | exact resolve b3e257 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e257
        have b3e298 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e244 X0 X1 x
             have i₂ := b3e12 X0 X1 x
             grind)
          | exact superpose b3e12 b3e244
          | exact resolve b3e244 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e244
        have b3e301 : ∀ X0 : G, (M.op (M.op X0 y) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e298 X0 x
             have i₂ := b3e46 X0 x
             grind)
          | exact superpose b3e46 b3e298
          | exact resolve b3e298 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e298
        have b3e312 : ∀ X0 X1 : G, (M.op X0 (k X0 y)) = (M.op (M.op (M.op X0 (k X0 y)) X0) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e31 X0 X0 x
             have i₂ := b3e75 X0
             grind)
          | exact superpose b3e75 b3e31
          | exact resolve b3e31 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e371 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) X0) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e312 X0 X1
             have i₂ := b3e290 X0 X0
             grind)
          | exact superpose b3e290 b3e312
          | exact resolve b3e312 b3e290
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e312
        have b3e392 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e371 X0 X1
             have i₂ := b3e301 X0
             grind)
          | exact superpose b3e301 b3e371
          | exact resolve b3e371 b3e301
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e301 b3e371
        have b3e713 : ∀ X0 : G, (k X0 y) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e84 X0
             have i₂ := b3e196 X0
             grind)
          | (have i₁ := b3e84 (σ y)
             have i₂ := b3e196 (σ y)
             grind)
          | exact superpose b3e196 b3e84
          | exact resolve b3e84 b3e196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e84
        have b3e726 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e196 (σ X0)
             grind)
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e196 (σ X0)
             grind)
          | exact superpose b3e196 b3e18
          | exact resolve b3e18 b3e196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e196
        have b3e729 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e726 X0
             have i₂ := b3e18 X0 X0
             grind)
          | exact superpose b3e18 b3e726
          | exact resolve b3e726 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e726
        have b3e741 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e729 X0
             have i₂ := b3e57 X0
             grind)
          | exact superpose b3e57 b3e729
          | exact resolve b3e729 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57 b3e729
        have b3e1053 : ∀ X0 : G, (k (σ X0) y) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e713 (σ X0)
             grind)
          | exact superpose b3e713 b3e18
          | exact resolve b3e18 b3e713
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1495 : ∀ X0 : G, (M.op (M.op X0 y) y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e33 X0 x
             have i₂ := b3e46 X0 x
             grind)
          | exact superpose b3e46 b3e33
          | exact resolve b3e33 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e46
        have b3e2376 : ∀ X0 : G, (M.op (k X0 y) y) = (k (k X0 y) y) := by
          intro X0
          first
          | (have i₁ := b3e75 (k X0 y)
             have i₂ := b3e290 X0 (k X0 y)
             grind)
          | exact superpose b3e290 b3e75
          | exact resolve b3e75 b3e290
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2932 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (k (M.op X0 X0) y) := by
          intro X0
          first
          | (have i₁ := b3e75 (M.op X0 X0)
             have i₂ := b3e392 (M.op X0 X0) X0
             grind)
          | exact superpose b3e392 b3e75
          | exact resolve b3e75 b3e392
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e392
        have b3e3353 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ (M.op X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e290 (σ X0) X1
             have i₂ := b3e193 X0
             grind)
          | exact superpose b3e193 b3e290
          | exact resolve b3e290 b3e193
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e290
        have b3e3530 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e29 X0 y
             have i₂ := b3e713 X0
             grind)
          | exact superpose b3e713 b3e29
          | exact resolve b3e29 b3e713
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e713
        have b3e3744 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (k (σ X0) y) (k (σ X0) y)) := by
          intro X0
          first
          | (have i₁ := b3e70 (M.op X0 X0)
             have i₂ := b3e193 X0
             grind)
          | exact superpose b3e193 b3e70
          | exact resolve b3e70 b3e193
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e3843 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (k (σ X0) y) y) := by
          intro X0
          first
          | (have i₁ := b3e3744 X0
             have i₂ := b3e75 (k (σ X0) y)
             grind)
          | exact superpose b3e75 b3e3744
          | exact resolve b3e3744 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75 b3e3744
        have b3e3854 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (k (σ X0) y) y) := by
          intro X0
          first
          | (have i₁ := b3e3843 X0
             have i₂ := b3e2376 (σ X0)
             grind)
          | exact superpose b3e2376 b3e3843
          | exact resolve b3e3843 b3e2376
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2376 b3e3843
        have b3e3860 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (k X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b3e3854 X0
             have i₂ := b3e1053 X0
             grind)
          | exact superpose b3e1053 b3e3854
          | exact resolve b3e3854 b3e1053
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3854
        have b3e3865 : ∀ X0 : G, (k (σ (M.op X0 X0)) y) = (M.op (σ (k X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b3e3860 X0
             have i₂ := b3e193 (M.op X0 X0)
             grind)
          | exact superpose b3e193 b3e3860
          | exact resolve b3e3860 b3e193
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e193 b3e3860
        have b3e3866 : ∀ X0 : G, (σ (k (M.op X0 X0) y)) = (M.op (σ (k X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b3e3865 X0
             have i₂ := b3e1053 (M.op X0 X0)
             grind)
          | exact superpose b3e1053 b3e3865
          | exact resolve b3e3865 b3e1053
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3865
        have b3e3867 : ∀ X0 : G, (σ (M.op (M.op X0 X0) y)) = (M.op (σ (k X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b3e3866 X0
             have i₂ := b3e2932 X0
             grind)
          | exact superpose b3e2932 b3e3866
          | exact resolve b3e3866 b3e2932
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3866
        have b3e17254 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e3353 y X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e3353
          | exact resolve b3e3353 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3353
        have b3e18540 : (M.op (σ x) (σ x)) = (M.op (σ x) y) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e17254 (σ x)
             grind)
          | exact superpose b3e17254 b3e22
          | exact resolve b3e22 b3e17254
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e17254
        have b3e18689 : (σ (M.op x x)) = (M.op (σ x) y) := by
          first
          | (have i₁ := b3e18540
             have i₂ := b3e70 x
             grind)
          | exact superpose b3e70 b3e18540
          | exact resolve b3e18540 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70 b3e18540
        have b3e20107 : (M.op x x) = (τ (M.op (σ x) y)) := by
          first
          | (have i₁ := b3e13 (M.op x x)
             have i₂ := b3e18689
             grind)
          | exact superpose b3e18689 b3e13
          | exact resolve b3e13 b3e18689
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e20125 : (σ (k (M.op x x) y)) = (k (M.op (σ x) y) y) := by
          first
          | (have i₁ := b3e1053 (M.op x x)
             have i₂ := b3e18689
             grind)
          | exact superpose b3e18689 b3e1053
          | exact resolve b3e1053 b3e18689
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1053
        have b3e20129 : (σ (M.op (M.op x x) y)) = (k (M.op (σ x) y) y) := by
          first
          | (have i₁ := b3e20125
             have i₂ := b3e2932 x
             grind)
          | exact superpose b3e2932 b3e20125
          | exact resolve b3e20125 b3e2932
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e20125
        have b3e20137 : (M.op (σ (k x y)) y) = (k (M.op (σ x) y) y) := by
          first
          | (have i₁ := b3e20129
             have i₂ := b3e3867 x
             grind)
          | exact superpose b3e3867 b3e20129
          | exact resolve b3e20129 b3e3867
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3867 b3e20129
        have b3e20142 : (M.op (σ (M.op x x)) y) = (k (M.op (σ x) y) y) := by
          first
          | (have i₁ := b3e20137
             have i₂ := b3e741 x
             grind)
          | exact superpose b3e741 b3e20137
          | exact resolve b3e20137 b3e741
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e741 b3e20137
        have b3e20147 : (M.op (M.op (σ x) y) y) = (k (M.op (σ x) y) y) := by
          first
          | (have i₁ := b3e20142
             have i₂ := b3e18689
             grind)
          | exact superpose b3e18689 b3e20142
          | exact resolve b3e20142 b3e18689
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e18689 b3e20142
        have b3e20152 : (σ x) = (k (M.op (σ x) y) y) := by
          first
          | (have i₁ := b3e20147
             have i₂ := b3e1495 (σ x)
             grind)
          | exact superpose b3e1495 b3e20147
          | exact resolve b3e20147 b3e1495
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e20147
        have b3e25963 : (τ (σ x)) = (k (τ (M.op (σ x) y)) y) := by
          first
          | (have i₁ := b3e3530 (M.op (σ x) y)
             have i₂ := b3e20152
             grind)
          | exact superpose b3e20152 b3e3530
          | exact resolve b3e3530 b3e20152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3530 b3e20152
        have b3e25981 : (k (M.op x x) y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e25963
             have i₂ := b3e20107
             grind)
          | exact superpose b3e20107 b3e25963
          | exact resolve b3e25963 b3e20107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e20107 b3e25963
        have b3e25991 : x = (k (M.op x x) y) := by
          first
          | (have i₁ := b3e25981
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e25981
          | exact resolve b3e25981 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25981
        have b3e25995 : x = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b3e25991
             have i₂ := b3e2932 x
             grind)
          | exact superpose b3e2932 b3e25991
          | exact resolve b3e25991 b3e2932
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2932 b3e25991
        have b3e27822 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b3e1495 (M.op x x)
             have i₂ := b3e25995
             grind)
          | exact superpose b3e25995 b3e1495
          | exact resolve b3e1495 b3e25995
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1495 b3e25995
        have b3e27846 : False := by grind
        exact b3e27846
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
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
          have b4e30 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
               have i₂ := b4e13 X0 X1 (M.op X0 (M.op X0 X1))
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e31 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) y) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (σ y)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e59 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b4e17 X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 X0 y
               grind)
            | (have r₁ := b4e17 X0 y
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e62 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b4e59 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59
          have b4e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b4e62 X0
               have j1 := b4e16 X0 y
               grind)
            | (have r₁ := b4e62 y
               have r₂ := b4e16 y y
               grind)
            | (have r₁ := b4e62 X0
               have r₂ := b4e16 X0 y
               grind)
            | exact resolve b4e62 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62
          have b4e77 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e99 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e77 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77
          have b4e121 : ∀ X0 X1 : G, (k X0 y) ≠ X0 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X1 X0
               have i₂ := b4e64 X0
               grind)
            | exact superpose b4e64 b4e17
            | (have j0 := b4e17 X1 X0
               grind)
            | exact resolve b4e17 b4e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e133 : ∀ X0 X1 : G, (k X0 y) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e121 X0 X1
               have j1 := b4e16 X1 X0
               grind)
            | (have r₁ := b4e121 X1 X1
               have r₂ := b4e16 X1 X1
               grind)
            | (have r₁ := b4e121 X1 X0
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e121 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e121
          have b4e188 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e31 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))
               have i₂ := b4e13 X0 X1 (M.op X0 (M.op X0 X1))
               grind)
            | exact superpose b4e13 b4e31
            | exact resolve b4e31 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e245 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          clear b4e25
          have b4e299 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))
               have i₂ := b4e13 X0 X1 (M.op X0 (M.op X0 X1))
               grind)
            | exact superpose b4e13 b4e32
            | exact resolve b4e32 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e305 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e299 X0 x
               have i₂ := b4e188 X0 x
               grind)
            | exact superpose b4e188 b4e299
            | exact resolve b4e299 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e299
          have b4e384 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X3)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e30 (M.op X0 (M.op X0 X1)) (M.op x x) X3
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e30
            | exact resolve b4e30 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e401 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op X1 X0) ∨ (M.op X3 X3) = (M.op X3 X0) ∨ (M.op X3 X0) = (k X3 X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e30 X1 X2 X0
               have i₂ := b4e18 X3 X0
               grind)
            | exact superpose b4e18 b4e30
            | (have j1 := b4e18 X3 X0
               grind)
            | exact resolve b4e30 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30
          have b4e446 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (M.op X1 y) ∨ (M.op X3 X3) = (M.op X3 X0) ∨ (M.op X3 X0) = (k X3 X0) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e401 X0 X1 x X3
               have i₂ := b4e188 X1 x
               grind)
            | exact superpose b4e188 b4e401
            | (have j0 := b4e401 X0 X1 x X3
               grind)
            | exact resolve b4e401 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e401
          have b4e458 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e384 X0 X1 x
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e384
            | exact resolve b4e384 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e384
          have b4e462 : ∀ X0 : G, (M.op (M.op X0 y) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e458 X0 x
               have i₂ := b4e188 X0 x
               grind)
            | exact superpose b4e188 b4e458
            | exact resolve b4e458 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e458
          have b4e689 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e305 (σ x)
               grind)
            | exact superpose b4e305 b4e20
            | exact resolve b4e20 b4e305
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e785 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e64 X0
               have i₂ := b4e99 X1 X0
               grind)
            | exact superpose b4e99 b4e64
            | (have j1 := b4e99 X1 X0
               grind)
            | exact resolve b4e64 b4e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64
          have b4e805 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e99 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99
          have b4e816 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e805 X0 X1
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e805 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e805 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | exact resolve b4e805 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e805
          have b4e826 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e785 X0 X1
               have j1 := b4e133 X0 X1
               grind)
            | (have r₁ := b4e785 X0 X1
               have r₂ := b4e133 X0 X1
               grind)
            | exact resolve b4e785 b4e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e133 b4e785
          have b4e8436 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 y) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e188 X0 X0
               have i₂ := b4e816 X1 X0
               grind)
            | exact superpose b4e816 b4e188
            | (have j1 := b4e816 X1 X0
               grind)
            | exact resolve b4e188 b4e816
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e188 b4e816
          have b4e9598 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e826 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e826
          have b4e21782 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) y) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e23
               have i₂ := b4e446 (σ x) (σ x) X0
               grind)
            | exact superpose b4e446 b4e23
            | (have j1 := b4e446 (σ x) x X0
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e446 (σ y) x (σ x)
               grind)
            | exact resolve b4e23 b4e446
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e446
          have b4e22135 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) y) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b4e21782 X0
               have j1 := b4e9598 X0 (σ x)
               grind)
            | (have r₁ := b4e21782 (σ x)
               have r₂ := b4e9598 (σ x) (σ x)
               grind)
            | (have r₁ := b4e21782 X0
               have r₂ := b4e9598 X0 (σ x)
               grind)
            | exact resolve b4e21782 b4e9598
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9598 b4e21782
          have b4e22238 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b4e22135 X0
               grind)
            | (have r₁ := b4e22135 X0
               have r₂ := b4e305 (σ x)
               grind)
            | exact resolve b4e22135 b4e305
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e305 b4e22135
          have b4e22313 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e245 X0 x
               have i₂ := b4e22238 X0
               grind)
            | exact superpose b4e22238 b4e245
            | exact resolve b4e245 b4e22238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e245 b4e22238
          have b4e32168 : (τ (σ x)) = (k (τ (M.op (σ x) y)) x) := by
            first
            | (have i₁ := b4e22313 (M.op (σ x) y)
               have i₂ := b4e462 (σ x)
               grind)
            | exact superpose b4e462 b4e22313
            | exact resolve b4e22313 b4e462
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e462 b4e22313
          have b4e32195 : x = (k (τ (M.op (σ x) y)) x) := by
            first
            | (have i₁ := b4e32168
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e32168
            | exact resolve b4e32168 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32168
          have b4e488905 : x = (M.op (τ (M.op (σ x) y)) x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e32195
               have i₂ := b4e8436 x (τ (M.op (σ x) y))
               grind)
            | exact superpose b4e8436 b4e32195
            | (have j1 := b4e8436 x x
               grind)
            | exact resolve b4e32195 b4e8436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8436 b4e32195
          have b4e488913 : x = (M.op (τ (M.op (σ x) y)) x) := by
            first
            | (have r₁ := b4e488905
               have r₂ := b4e21
               grind)
            | exact resolve b4e488905 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e488905
          have b4e489060 : (τ (M.op (σ x) y)) = (M.op (M.op (τ (M.op (σ x) y)) x) y) := by
            first
            | (have i₁ := b4e31 (τ (M.op (σ x) y)) x
               have i₂ := b4e488913
               grind)
            | exact superpose b4e488913 b4e31
            | exact resolve b4e31 b4e488913
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e489093 : (M.op x y) = (τ (M.op (σ x) y)) := by
            first
            | (have i₁ := b4e489060
               have i₂ := b4e488913
               grind)
            | exact superpose b4e488913 b4e489060
            | exact resolve b4e489060 b4e488913
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e488913 b4e489060
          have b4e491697 : (σ (M.op x y)) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e15 (M.op (σ x) y)
               have i₂ := b4e489093
               grind)
            | exact superpose b4e489093 b4e15
            | exact resolve b4e15 b4e489093
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e489093
          have b4e491716 : False := by grind
          exact b4e491716
        · have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e62 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b5e17 X0 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 X0 y
               grind)
            | (have r₁ := b5e17 X0 y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b5e62 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b5e63 X0
               have j1 := b5e16 X0 y
               grind)
            | (have r₁ := b5e63 y
               have r₂ := b5e16 y y
               grind)
            | (have r₁ := b5e63 X0
               have r₂ := b5e16 X0 y
               grind)
            | exact resolve b5e63 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e107 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ y)
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 X0 (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e112 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e107 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e107
          have b5e142 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e25 X0 (τ X0)
               have i₂ := b5e51 (τ X0)
               grind)
            | exact superpose b5e51 b5e25
            | exact resolve b5e25 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e148 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (k (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b5e142 X0
               have i₂ := b5e64 (τ X0)
               grind)
            | exact superpose b5e64 b5e142
            | exact resolve b5e142 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64 b5e142
          have b5e149 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e148 X0
               have i₂ := b5e25 X0 y
               grind)
            | exact superpose b5e25 b5e148
            | exact resolve b5e148 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e148
          have b5e150 : ∀ X0 : G, (k X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e149 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e149
            | exact resolve b5e149 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e149
          have b5e535 : ∀ X0 : G, (k X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e112 X0
               have i₂ := b5e150 X0
               grind)
            | (have i₁ := b5e112 (σ y)
               have i₂ := b5e150 (σ y)
               grind)
            | exact superpose b5e150 b5e112
            | (have j0 := b5e112 X0
               grind)
            | exact resolve b5e112 b5e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e112 b5e150
          have b5e544 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e535 X0
               have i₂ := b5e51 X0
               grind)
            | exact superpose b5e51 b5e535
            | (have j0 := b5e535 X0
               grind)
            | exact resolve b5e535 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51 b5e535
          have b5e545 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e544 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e544
          have b5e1079 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e545 (σ x)
               grind)
            | exact superpose b5e545 b5e23
            | (have r₁ := b5e23
               have r₂ := b5e545 (σ x)
               grind)
            | exact resolve b5e23 b5e545
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e545
          have b5e1088 : False := by grind
          exact b5e1088
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op y y) := by grind
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
        have b6e50 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e52 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e50
        have b6e53 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e52
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e52
          | exact resolve b6e52 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e68 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e53
             grind)
          | exact superpose b6e53 b6e23
          | exact resolve b6e23 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e53
        have b6e124 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
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
        have b6e125 : (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by grind
        clear b6e124
        have b6e126 : y = (M.op y y) := by
          first
          | (have r₁ := b6e125
             have r₂ := b6e20
             grind)
          | exact resolve b6e125 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e125
        have b6e127 : False := by grind
        exact b6e127
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e40 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e45 : (σ y) = (k (σ y) (σ y)) := by grind
          clear b7e40
          have b7e47 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e45
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e45
            | exact resolve b7e45 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e49 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e44 y
               grind)
            | exact superpose b7e44 b7e47
            | exact resolve b7e47 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44 b7e47
          have b7e62 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e49
               grind)
            | exact superpose b7e49 b7e14
            | exact resolve b7e14 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e63 : y = (M.op y y) := by
            first
            | (have i₁ := b7e62
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e62
            | exact resolve b7e62 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e66 : False := by grind
          exact b7e66
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
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
          have b8e87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
          have b8e97 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e87 X0 X1
               have i₂ := b8e49 X0
               grind)
            | exact superpose b8e49 b8e87
            | (have j0 := b8e87 X0 X1
               grind)
            | exact resolve b8e87 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e87
          have b8e104 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e97 X0 X1
               have i₂ := b8e49 X1
               grind)
            | exact superpose b8e49 b8e97
            | (have j0 := b8e97 X0 X1
               grind)
            | exact resolve b8e97 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e97
          have b8e272 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e49 y
               grind)
            | exact superpose b8e49 b8e24
            | exact resolve b8e24 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e273 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e49 x
               grind)
            | exact superpose b8e49 b8e23
            | exact resolve b8e23 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49
          have b8e2067 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e104 x y
               grind)
            | exact superpose b8e104 b8e20
            | (have j1 := b8e104 x y
               grind)
            | exact resolve b8e20 b8e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104
          have b8e2130 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e2067
               have r₂ := b8e272
               grind)
            | exact resolve b8e2067 b8e272
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e272 b8e2067
          have b8e2170 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e2130
               have r₂ := b8e273
               grind)
            | exact resolve b8e2130 b8e273
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e273 b8e2130
          have b8e2206 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e2170
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e2170
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e2170 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2170
          have b8e2211 : (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e2206
          have b8e2213 : y = (M.op y y) := by
            first
            | (have r₁ := b8e2211
               have r₂ := b8e21
               grind)
            | exact resolve b8e2211 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2211
          have b8e2214 : False := by grind
          exact b8e2214

/-- `Equation2503`: `x = (y ◇ ((x ◇ y) ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pxx_pyy_pyx_Equation2503 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2503 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2503.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
      have b0e29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
      have b0e36 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e49 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
        intro X0
        first
        | (have i₁ := b0e22 X0 (τ X0)
           have i₂ := b0e41 (τ X0)
           grind)
        | exact superpose b0e41 b0e22
        | exact resolve b0e22 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e50 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e49 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e49
        | exact resolve b0e49 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49
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
      clear b0e47
      have b0e54 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e50 X0
           have i₂ := b0e41 X0
           grind)
        | exact superpose b0e41 b0e50
        | exact resolve b0e50 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e50
      have b0e64 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 X0
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e14 X1 X1
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X0
           have j1 := b0e16 X1 X0
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | (have r₁ := b0e14 X1 X1
           have r₂ := b0e16 X1 X1
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e70 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X0 X1
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e15 X0 X0
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e15
        | (have j0 := b0e15 X0 X1
           have j1 := b0e16 X0 X1
           grind)
        | (have r₁ := b0e15 X1 X1
           have r₂ := b0e16 X1 X1
           grind)
        | (have r₁ := b0e15 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | (have r₁ := b0e15 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | exact resolve b0e15 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
      have b0e82 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e16 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e85 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e70 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70
      have b0e87 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e64 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e64
      have b0e89 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e78 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e78
        | (have j0 := b0e78 X0 X1
           grind)
        | exact resolve b0e78 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78
      have b0e91 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e85 X0 X1
           have j1 := b0e82 X1 X0
           grind)
        | (have r₁ := b0e85 X0 X1
           have r₂ := b0e82 X0 X1
           grind)
        | (have r₁ := b0e85 X1 X0
           have r₂ := b0e82 X0 X1
           grind)
        | (have r₁ := b0e85 X0 X0
           have r₂ := b0e82 X0 X0
           grind)
        | exact resolve b0e85 b0e82
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e82 b0e85
      have b0e94 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e89 X0 X1
           have i₂ := b0e52 X1
           grind)
        | exact superpose b0e52 b0e89
        | (have j0 := b0e89 X0 X1
           grind)
        | exact resolve b0e89 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e89
      have b0e108 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e29 X1 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e29
        | exact resolve b0e29 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e165 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 (σ X0)
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e14
        | (have j0 := b0e14 X1 (σ X0)
           grind)
        | exact resolve b0e14 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e187 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e12 (M.op (τ X0) (τ X0))
           have i₂ := b0e54 X0
           grind)
        | exact superpose b0e54 b0e12
        | exact resolve b0e12 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e251 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e21 X0 X1
           have i₂ := b0e87 X1 (τ X0)
           grind)
        | exact superpose b0e87 b0e21
        | (have j1 := b0e87 X1 (τ X0)
           grind)
        | exact resolve b0e21 b0e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87
      have b0e269 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e251 X0 X1
           have i₂ := b0e54 X0
           grind)
        | exact superpose b0e54 b0e251
        | (have j0 := b0e251 X0 X1
           grind)
        | exact resolve b0e251 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e251
      have b0e286 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e269 X0 X1
           have i₂ := b0e187 X0
           grind)
        | exact superpose b0e187 b0e269
        | (have j0 := b0e269 X0 X1
           grind)
        | exact resolve b0e269 b0e187
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e269
      have b0e308 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 (τ X0)
           have i₂ := b0e187 X0
           grind)
        | exact superpose b0e187 b0e14
        | (have j0 := b0e14 X1 (τ X0)
           grind)
        | exact resolve b0e14 b0e187
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e334 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e91 (σ X0) (σ X1)
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e91
        | (have j0 := b0e91 (σ X0) (σ X1)
           grind)
        | exact resolve b0e91 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e358 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e22 X0 X1
           have i₂ := b0e91 X1 (τ X0)
           grind)
        | exact superpose b0e91 b0e22
        | (have j1 := b0e91 X1 (τ X0)
           grind)
        | exact resolve b0e22 b0e91
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e367 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e21 X1 X0
           have i₂ := b0e91 (τ X1) X0
           grind)
        | exact superpose b0e91 b0e21
        | (have j1 := b0e91 (τ X1) X0
           grind)
        | exact resolve b0e21 b0e91
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e91
      have b0e385 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e358 X0 X1
           have i₂ := b0e54 X0
           grind)
        | exact superpose b0e54 b0e358
        | (have j0 := b0e358 X0 X1
           grind)
        | exact resolve b0e358 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e358
      have b0e394 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e334 X0 X1
           have i₂ := b0e52 X1
           grind)
        | exact superpose b0e52 b0e334
        | (have j0 := b0e334 X0 X1
           grind)
        | exact resolve b0e334 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e334
      have b0e405 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e385 X0 X1
           have i₂ := b0e187 X0
           grind)
        | exact superpose b0e187 b0e385
        | (have j0 := b0e385 X0 X1
           grind)
        | exact resolve b0e385 b0e187
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e187 b0e385
      have b0e409 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e394 X0 X1
           have i₂ := b0e52 X1
           grind)
        | exact superpose b0e52 b0e394
        | (have j0 := b0e394 X0 X1
           grind)
        | exact resolve b0e394 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e394
      have b0e1460 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (σ X0) (σ X1)
           have i₂ := b0e94 X1 X0
           grind)
        | exact superpose b0e94 b0e14
        | (have j0 := b0e14 (σ X0) (σ X1)
           have j1 := b0e94 X1 X0
           grind)
        | exact resolve b0e14 b0e94
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1493 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e94 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1494 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e94 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e94
      have b0e1541 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e1460 X0 X1
           have j1 := b0e165 X1 (σ X0)
           grind)
        | (have r₁ := b0e1460 X0 X0
           have r₂ := b0e165 X0 (σ X0)
           grind)
        | (have r₁ := b0e1460 X0 X0
           have r₂ := b0e165 X0 (σ X0)
           grind)
        | exact resolve b0e1460 b0e165
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e165 b0e1460
      have b0e1595 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1541 X0 X1
           have i₂ := b0e52 X1
           grind)
        | exact superpose b0e52 b0e1541
        | (have j0 := b0e1541 X0 X1
           grind)
        | exact resolve b0e1541 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1541
      have b0e1631 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1595 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e1595
        | (have j0 := b0e1595 X0 X1
           grind)
        | exact resolve b0e1595 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1595
      have b0e1653 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1631 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e1631
        | (have j0 := b0e1631 X0 X1
           grind)
        | exact resolve b0e1631 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1631
      have b0e7895 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e13 (M.op X1 X1)
           have i₂ := b0e286 X1 X0
           grind)
        | exact superpose b0e286 b0e13
        | (have j1 := b0e286 X1 X0
           grind)
        | exact resolve b0e13 b0e286
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e286
      have b0e9261 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e367 X0 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e367
        | exact resolve b0e367 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e367
      have b0e9521 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e9261 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e9261
        | (have j0 := b0e9261 X0 X1
           grind)
        | exact resolve b0e9261 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9261
      have b0e9974 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e308 X0 X1
           have i₂ := b0e405 X0 X1
           grind)
        | exact superpose b0e405 b0e308
        | (have j0 := b0e308 X0 X1
           have j1 := b0e405 X0 X1
           grind)
        | (have r₁ := b0e308 X0 X1
           have r₂ := b0e405 X0 X1
           grind)
        | exact resolve b0e308 b0e405
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e308
      have b0e10017 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e13 (M.op X0 X0)
           have i₂ := b0e405 X0 X1
           grind)
        | exact superpose b0e405 b0e13
        | (have j1 := b0e405 X0 X1
           grind)
        | exact resolve b0e13 b0e405
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e405
      have b0e10178 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have j0 := b0e9974 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9974
      have b0e15962 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e1653 (τ X1) (τ X0)
           have i₂ := b0e108 X0 X1
           grind)
        | exact superpose b0e108 b0e1653
        | (have j0 := b0e1653 (τ X0) (τ X1)
           grind)
        | exact resolve b0e1653 b0e108
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1653
      have b0e16069 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e15962 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e15962
        | (have j0 := b0e15962 X0 X1
           grind)
        | exact resolve b0e15962 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15962
      have b0e16108 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e16069 X0 X1
           have i₂ := b0e54 X1
           grind)
        | exact superpose b0e54 b0e16069
        | (have j0 := b0e16069 X0 X1
           grind)
        | exact resolve b0e16069 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16069
      have b0e16142 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e16108 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e16108
        | (have j0 := b0e16108 X0 X1
           grind)
        | exact resolve b0e16108 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16108
      have b0e16165 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e16142 X0 X1
           have i₂ := b0e54 X0
           grind)
        | exact superpose b0e54 b0e16142
        | (have j0 := b0e16142 X0 X1
           grind)
        | exact resolve b0e16142 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16142
      have b0e16182 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e16165 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e16165
        | (have j0 := b0e16165 X0 X1
           grind)
        | exact resolve b0e16165 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16165
      have b0e16194 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e16182 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e16182
        | (have j0 := b0e16182 X0 X1
           grind)
        | exact resolve b0e16182 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16182
      have b0e16202 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e16194 X0 X1
           have i₂ := b0e54 X0
           grind)
        | exact superpose b0e54 b0e16194
        | (have j0 := b0e16194 X0 X1
           grind)
        | exact resolve b0e16194 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16194
      have b0e18202 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 (σ X0) (σ X1)
           have i₂ := b0e409 X0 X1
           grind)
        | exact superpose b0e409 b0e15
        | (have j0 := b0e15 (σ X0) (σ X1)
           have j1 := b0e409 X0 X1
           grind)
        | exact resolve b0e15 b0e409
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e18369 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e18202 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e18202
        | (have j0 := b0e18202 X0 X1
           grind)
        | exact resolve b0e18202 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18202
      have b0e18511 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e18369 X0 X1
           have i₂ := b0e52 X1
           grind)
        | exact superpose b0e52 b0e18369
        | (have j0 := b0e18369 X0 X1
           grind)
        | exact resolve b0e18369 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18369
      have b0e18512 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e18511 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18511
      have b0e18606 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e18512 X0 X1
           have i₂ := b0e52 X1
           grind)
        | exact superpose b0e52 b0e18512
        | (have j0 := b0e18512 X0 X1
           grind)
        | exact resolve b0e18512 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18512
      have b0e18644 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e18606 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e18606
        | (have j0 := b0e18606 X0 X1
           grind)
        | exact resolve b0e18606 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18606
      have b0e18645 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e18644 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18644
      have b0e81636 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e21 X0 (τ X1)
           have i₂ := b0e10178 X1 (τ X0)
           grind)
        | exact superpose b0e10178 b0e21
        | (have j1 := b0e10178 X1 (τ X0)
           grind)
        | exact resolve b0e21 b0e10178
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21
      have b0e81685 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e29 (σ X1) X0
           have i₂ := b0e10178 (σ X0) X1
           grind)
        | exact superpose b0e10178 b0e29
        | (have j1 := b0e10178 (σ X0) X1
           grind)
        | exact resolve b0e29 b0e10178
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10178
      have b0e81695 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e81685 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e81685
        | (have j0 := b0e81685 X0 X1
           grind)
        | exact resolve b0e81685 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81685
      have b0e81708 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e81636 X0 X1
           have i₂ := b0e54 X0
           grind)
        | exact superpose b0e54 b0e81636
        | (have j0 := b0e81636 X0 X1
           grind)
        | exact resolve b0e81636 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54 b0e81636
      have b0e81734 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e81695 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e81695
        | (have j0 := b0e81695 X0 X1
           grind)
        | exact resolve b0e81695 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81695
      have b0e81739 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e81708 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e81708
        | (have j0 := b0e81708 X0 X1
           grind)
        | exact resolve b0e81708 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81708
      have b0e81756 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e81734 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e81734
        | (have j0 := b0e81734 X0 X1
           grind)
        | exact resolve b0e81734 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81734
      have b0e81761 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e81739 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e81739
        | (have j0 := b0e81739 X0 X1
           grind)
        | exact resolve b0e81739 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81739
      have b0e81771 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e81756 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e81756
        | (have j0 := b0e81756 X0 X1
           grind)
        | exact resolve b0e81756 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81756
      have b0e81774 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e81761 X0 X1
           have i₂ := b0e108 X1 X0
           grind)
        | exact superpose b0e108 b0e81761
        | (have j0 := b0e81761 X0 X1
           grind)
        | exact resolve b0e81761 b0e108
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108 b0e81761
      have b0e81778 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e81771 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e81771
        | (have j0 := b0e81771 X0 X1
           grind)
        | exact resolve b0e81771 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81771
      have b0e82989 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e29 X1 X0
           have i₂ := b0e81778 (σ X0) X1
           grind)
        | exact superpose b0e81778 b0e29
        | (have j1 := b0e81778 (σ X0) X1
           grind)
        | exact resolve b0e29 b0e81778
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81778
      have b0e83094 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e82989 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e82989
        | (have j0 := b0e82989 X0 X1
           grind)
        | exact resolve b0e82989 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e82989
      have b0e83233 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e83094 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e83094
        | (have j0 := b0e83094 X0 X1
           grind)
        | exact resolve b0e83094 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83094
      have b0e90301 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e16202 X0 X1
           have i₂ := b0e81774 X0 X1
           grind)
        | exact superpose b0e81774 b0e16202
        | (have j0 := b0e16202 X1 X0
           have j1 := b0e81774 X1 X0
           grind)
        | (have r₁ := b0e16202 X0 X1
           have r₂ := b0e81774 X0 X1
           grind)
        | (have r₁ := b0e16202 X1 X1
           have r₂ := b0e81774 X1 X1
           grind)
        | exact resolve b0e16202 b0e81774
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e90386 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e81774 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81774
      have b0e90400 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e90301 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e90301
      have b0e90476 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e90400 X0 X1
           have j1 := b0e90386 X1 X0
           grind)
        | (have r₁ := b0e90400 X0 X1
           have r₂ := b0e90386 X0 X1
           grind)
        | (have r₁ := b0e90400 X1 X0
           have r₂ := b0e90386 X0 X1
           grind)
        | (have r₁ := b0e90400 X0 X0
           have r₂ := b0e90386 X0 X0
           grind)
        | exact resolve b0e90400 b0e90386
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e90386 b0e90400
      have b0e104223 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e90476 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e90476
        | (have j0 := b0e90476 (σ X0) X1
           grind)
        | exact resolve b0e90476 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e90476
      have b0e104288 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e104223 X0 X1
           have i₂ := b0e29 X1 X0
           grind)
        | exact superpose b0e29 b0e104223
        | (have j0 := b0e104223 X0 X1
           grind)
        | exact resolve b0e104223 b0e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29 b0e104223
      have b0e135947 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e36 X0 (σ X1)
           have i₂ := b0e83233 X1 (σ X0)
           grind)
        | exact superpose b0e83233 b0e36
        | (have j1 := b0e83233 X1 (σ X0)
           grind)
        | exact resolve b0e36 b0e83233
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83233
      have b0e136004 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e135947 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e135947
        | (have j0 := b0e135947 X0 X1
           grind)
        | exact resolve b0e135947 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e135947
      have b0e136031 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e136004 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e136004
        | (have j0 := b0e136004 X0 X1
           grind)
        | exact resolve b0e136004 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e136004
      have b0e136048 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e136031 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e136031
        | (have j0 := b0e136031 X0 X1
           grind)
        | exact resolve b0e136031 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e136031
      have b0e136061 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e136048 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e136048
        | (have j0 := b0e136048 X0 X1
           grind)
        | exact resolve b0e136048 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e136048
      have b0e136066 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e136061 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e136061
        | (have j0 := b0e136061 X0 X1
           grind)
        | exact resolve b0e136061 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e136061
      have b0e139748 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e136066 y x
           grind)
        | exact superpose b0e136066 b0e18
        | (have j1 := b0e136066 y x
           grind)
        | exact resolve b0e18 b0e136066
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e136066
      have b0e140315 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e139748
           have i₂ := b0e16 y x
           grind)
        | exact superpose b0e16 b0e139748
        | (have j1 := b0e16 y x
           grind)
        | exact resolve b0e139748 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e140320 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e139748
           have i₂ := b0e9521 y x
           grind)
        | exact superpose b0e9521 b0e139748
        | (have j1 := b0e9521 y x
           grind)
        | (have r₁ := b0e139748
           have r₂ := b0e9521 y x
           grind)
        | exact resolve b0e139748 b0e9521
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9521 b0e139748
      have b0e140327 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e140320
      have b0e140328 : (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e140327
      have b0e140333 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e140315
      have b0e140334 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e140333
      have b0e140336 : (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
        first
        | (have j1 := b0e14 y x
           grind)
        | (have r₁ := b0e140328
           have r₂ := b0e14 y x
           grind)
        | exact resolve b0e140328 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e140328
      have b0e142701 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e16202 y x
           have i₂ := b0e140336
           grind)
        | exact superpose b0e140336 b0e16202
        | (have j0 := b0e16202 y x
           grind)
        | (have r₁ := b0e16202 y x
           have r₂ := b0e140336
           grind)
        | exact resolve b0e16202 b0e140336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16202
      have b0e142717 : (M.op y y) ≠ (M.op x x) ∨ (M.op y y) = (k y x) := by grind
      have b0e142721 : (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by grind
      clear b0e142701
      have b0e142737 : (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have r₁ := b0e142721
           have r₂ := b0e142717
           grind)
        | exact resolve b0e142721 b0e142717
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e142721
      have b0e193332 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e36 X0 (σ X1)
           have i₂ := b0e104288 X1 (σ X0)
           grind)
        | exact superpose b0e104288 b0e36
        | (have j1 := b0e104288 X1 (σ X0)
           grind)
        | exact resolve b0e36 b0e104288
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e104288
      have b0e193337 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e193332 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e193332
        | (have j0 := b0e193332 X0 X1
           grind)
        | exact resolve b0e193332 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e193332
      have b0e193355 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e193337 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e193337
        | (have j0 := b0e193337 X0 X1
           grind)
        | exact resolve b0e193337 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e193337
      have b0e193366 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e193355 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e193355
        | (have j0 := b0e193355 X0 X1
           grind)
        | exact resolve b0e193355 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e193355
      have b0e193372 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e193366 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e193366
        | (have j0 := b0e193366 X0 X1
           grind)
        | exact resolve b0e193366 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e193366
      have b0e193373 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e193372 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e193372
        | (have j0 := b0e193372 X0 X1
           grind)
        | exact resolve b0e193372 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e193372
      have b0e198486 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e193373 y x
           grind)
        | exact superpose b0e193373 b0e18
        | (have j1 := b0e193373 y x
           grind)
        | exact resolve b0e18 b0e193373
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e193373
      have b0e304437 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e7895 X0 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e7895
        | (have j0 := b0e7895 X1 (σ X0)
           grind)
        | exact resolve b0e7895 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7895
      have b0e304461 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e304437 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e304437
        | (have j0 := b0e304437 X0 X1
           grind)
        | exact resolve b0e304437 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e304437
      have b0e304464 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e304461 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e304461
        | (have j0 := b0e304461 X0 X1
           grind)
        | exact resolve b0e304461 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e304461
      have b0e304467 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e304464 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e304464
        | (have j0 := b0e304464 X0 X1
           grind)
        | exact resolve b0e304464 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e304464
      have b0e304970 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e304467 y x
           have i₂ := b0e140336
           grind)
        | exact superpose b0e140336 b0e304467
        | (have j0 := b0e304467 y x
           grind)
        | exact resolve b0e304467 b0e140336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e140336 b0e304467
      have b0e305061 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op y y) = (k y x) := by
        first
        | (have j1 := b0e14 y x
           grind)
        | (have r₁ := b0e304970
           have r₂ := b0e14 y x
           grind)
        | exact resolve b0e304970 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e304970
      have b0e305706 : (M.op x x) = (τ (σ (M.op y y))) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e12 (M.op x x)
           have i₂ := b0e305061
           grind)
        | exact superpose b0e305061 b0e12
        | exact resolve b0e12 b0e305061
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e305061
      have b0e305742 : (M.op y y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e305706
           have i₂ := b0e12 (M.op y y)
           grind)
        | exact superpose b0e12 b0e305706
        | exact resolve b0e305706 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e305706
      have b0e305743 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op y y) = (k y x) := by
        first
        | (have r₁ := b0e305742
           have r₂ := b0e142717
           grind)
        | exact resolve b0e305742 b0e142717
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e142717 b0e305742
      have b0e305961 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e198486
           have i₂ := b0e305743
           grind)
        | exact superpose b0e305743 b0e198486
        | (have r₁ := b0e198486
           have r₂ := b0e305743
           grind)
        | exact resolve b0e198486 b0e305743
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e198486 b0e305743
      have b0e305986 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by grind
      clear b0e305961
      have b0e305987 : (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by grind
      clear b0e305986
      have b0e306141 : (M.op x y) ≠ (M.op y y) ∨ (M.op y y) = (k y x) := by grind
      clear b0e305987
      have b0e306150 : (M.op y y) = (k y x) := by
        first
        | (have r₁ := b0e306141
           have r₂ := b0e142737
           grind)
        | exact resolve b0e306141 b0e142737
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e142737 b0e306141
      have b0e306463 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e1493 x y
           have i₂ := b0e306150
           grind)
        | exact superpose b0e306150 b0e1493
        | (have j0 := b0e1493 x y
           grind)
        | exact resolve b0e1493 b0e306150
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1493
      have b0e306464 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e1494 x y
           have i₂ := b0e306150
           grind)
        | exact superpose b0e306150 b0e1494
        | (have j0 := b0e1494 x y
           grind)
        | exact resolve b0e1494 b0e306150
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1494
      have b0e306491 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
      clear b0e306464
      have b0e306492 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
      clear b0e306463
      have b0e324053 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e306491
           grind)
        | exact superpose b0e306491 b0e18
        | exact resolve b0e18 b0e306491
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e306491
      have b0e325524 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e324053
           have i₂ := b0e140334
           grind)
        | exact superpose b0e140334 b0e324053
        | exact resolve b0e324053 b0e140334
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e324053
      have b0e325529 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e325524
      have b0e327810 : (σ (M.op y y)) = (σ (k y x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e325529
           have i₂ := b0e409 y x
           grind)
        | exact superpose b0e409 b0e325529
        | (have j1 := b0e409 y x
           grind)
        | exact resolve b0e325529 b0e409
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e409
      have b0e327812 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e325529
           grind)
        | exact superpose b0e325529 b0e18
        | exact resolve b0e18 b0e325529
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e325529
      have b0e327829 : (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (k y x)) := by
        first
        | (have j1 := b0e18645 y x
           grind)
        | (have r₁ := b0e327810
           have r₂ := b0e18645 y x
           grind)
        | exact resolve b0e327810 b0e18645
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18645 b0e327810
      have b0e327832 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e327829
           have i₂ := b0e306150
           grind)
        | exact superpose b0e306150 b0e327829
        | exact resolve b0e327829 b0e306150
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e327829
      have b0e876364 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10017 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e10017
        | (have j0 := b0e10017 (σ X0) X1
           grind)
        | exact resolve b0e10017 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10017
      have b0e876370 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e876364 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e876364
        | (have j0 := b0e876364 X0 X1
           grind)
        | exact resolve b0e876364 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e876364
      have b0e876371 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e876370 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e876370
        | (have j0 := b0e876370 X0 X1
           grind)
        | exact resolve b0e876370 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52 b0e876370
      have b0e876372 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e876371 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e876371
        | (have j0 := b0e876371 X0 X1
           grind)
        | exact resolve b0e876371 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e876371
      have b0e887690 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e876372 x y
           have i₂ := b0e306150
           grind)
        | exact superpose b0e306150 b0e876372
        | (have j0 := b0e876372 x y
           grind)
        | exact resolve b0e876372 b0e306150
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e876372
      have b0e2714427 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e327832
           grind)
        | exact superpose b0e327832 b0e18
        | exact resolve b0e18 b0e327832
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e327832
      have b0e2714428 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have r₁ := b0e2714427
           have r₂ := b0e887690
           grind)
        | exact resolve b0e2714427 b0e887690
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e887690 b0e2714427
      have b0e2727368 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e2714428
           have i₂ := b0e140334
           grind)
        | exact superpose b0e140334 b0e2714428
        | exact resolve b0e2714428 b0e140334
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e140334 b0e2714428
      have b0e2727399 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e2727368
      have b0e2727418 : (M.op x y) = (M.op y y) := by
        first
        | (have r₁ := b0e2727399
           have r₂ := b0e327812
           grind)
        | exact resolve b0e2727399 b0e327812
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e327812 b0e2727399
      have b0e2742261 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e2727418
           grind)
        | exact superpose b0e2727418 b0e15
        | (have j0 := b0e15 y y
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e2727418
           grind)
        | exact resolve b0e15 b0e2727418
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2742296 : (M.op y y) = (M.op x x) ∨ (M.op x x) = (k y x) := by grind
      clear b0e2742261
      have b0e2742299 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
        first
        | (have i₁ := b0e2742296
           have i₂ := b0e306150
           grind)
        | exact superpose b0e306150 b0e2742296
        | exact resolve b0e2742296 b0e306150
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e306150 b0e2742296
      have b0e2742300 : (M.op y y) = (M.op x x) := by grind
      clear b0e2742299
      have b0e2752775 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e306492
           have i₂ := b0e2742300
           grind)
        | exact superpose b0e2742300 b0e306492
        | exact resolve b0e306492 b0e2742300
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e306492 b0e2742300
      have b0e2753056 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
      clear b0e2752775
      have b0e2763521 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e2753056
           grind)
        | exact superpose b0e2753056 b0e18
        | exact resolve b0e18 b0e2753056
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2753056
      have b0e2763554 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e2763521
           have i₂ := b0e2727418
           grind)
        | exact superpose b0e2727418 b0e2763521
        | exact resolve b0e2763521 b0e2727418
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2727418 b0e2763521
      have b0e2763555 : False := by grind
      exact b0e2763555
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : (M.op y x) = (M.op y y) := by grind
        have b1e21 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e49 : (M.op y y) ≠ (M.op y y) ∨ (k x y) = (M.op x x) := by
          first
          | (have i₁ := b1e15 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 y y
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
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
        have b1e53 : (M.op (σ y) (σ x)) = (k (σ x) (σ x)) := by grind
        clear b1e50
        have b1e54 : (k x y) = (M.op x x) := by grind
        clear b1e49
        have b1e55 : (M.op (σ y) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e53
          | exact resolve b1e53 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e56 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e55
             have i₂ := b1e52 x
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
        have b1e72 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e16 (σ x) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) X0
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e74 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e72 X0
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e72
          | (have j0 := b1e72 X0
             grind)
          | exact resolve b1e72 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72
        have b1e123 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e21
          | exact resolve b1e21 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e127 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e123
             have i₂ := b1e65 y
             grind)
          | exact superpose b1e65 b1e123
          | exact resolve b1e123 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e123
        have b1e592 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e74 (σ y)
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e74
          | (have j0 := b1e74 (σ y)
             grind)
          | (have r₁ := b1e74 (σ y)
             have r₂ := b1e56
             grind)
          | exact resolve b1e74 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e74
        have b1e593 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e592
        have b1e594 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e593
             have i₂ := b1e65 y
             grind)
          | exact superpose b1e65 b1e593
          | exact resolve b1e593 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e593
        have b1e597 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e594
             have r₂ := b1e127
             grind)
          | exact resolve b1e594 b1e127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e594
        have b1e600 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e597
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e597
          | exact resolve b1e597 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e597
        have b1e602 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e600
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e600
          | exact resolve b1e600 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54 b1e600
        have b1e604 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e602
             have i₂ := b1e65 y
             grind)
          | exact superpose b1e65 b1e602
          | exact resolve b1e602 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65 b1e602
        have b1e605 : False := by grind
        exact b1e605
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op y x) = (M.op y y) := by grind
        have b2e21 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e48 : (M.op y y) ≠ (M.op y y) ∨ (k x y) = (M.op x x) := by
          first
          | (have i₁ := b2e15 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 y y
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
        have b2e50 : (k x y) = (M.op x x) := by grind
        clear b2e48
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
        have b2e87 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) (σ x)
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
        have b2e134 : (M.op (σ y) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e59 x
             grind)
          | exact superpose b2e59 b2e22
          | exact resolve b2e22 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e1035 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e87 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87
        have b2e1036 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1035
             have r₂ := b2e21
             grind)
          | exact resolve b2e1035 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1035
        have b2e1040 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1036
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1036
          | exact resolve b2e1036 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1036
        have b2e1043 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1040
             have i₂ := b2e50
             grind)
          | exact superpose b2e50 b2e1040
          | exact resolve b2e1040 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50 b2e1040
        have b2e1044 : False := by grind
        exact b2e1044
  · rcases eq_or_ne (M.op x x) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op y x) ≠ (M.op y y) := by grind
        have b3e21 : (M.op y x) = (M.op x x) := by grind
        have b3e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e50 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ y) (σ y)
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
        have b3e53 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b3e50
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
        have b3e72 : ∀ X0 : G, (M.op y x) ≠ (M.op X0 x) ∨ (M.op X0 X0) = (M.op X0 x) ∨ (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e16 x X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 x X0
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e76 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e55
             grind)
          | exact superpose b3e55 b3e15
          | exact resolve b3e15 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e78 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b3e76
        have b3e79 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e78
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e78
          | exact resolve b3e78 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78
        have b3e80 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e79
             have i₂ := b3e52 x
             grind)
          | exact superpose b3e52 b3e79
          | exact resolve b3e79 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52 b3e79
        have b3e81 : (σ (k x y)) = (σ (M.op y x)) := by
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
        have b3e129 : (k x y) = (τ (σ (M.op y x))) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e81
             grind)
          | exact superpose b3e81 b3e13
          | exact resolve b3e13 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81
        have b3e130 : (M.op y x) = (k x y) := by
          first
          | (have i₁ := b3e129
             have i₂ := b3e13 (M.op y x)
             grind)
          | exact superpose b3e13 b3e129
          | exact resolve b3e129 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e129
        have b3e218 : (M.op y x) = (M.op y y) ∨ (M.op y y) = (k x y) := by
          first
          | (have j0 := b3e72 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72
        have b3e219 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b3e218
             have r₂ := b3e20
             grind)
          | exact resolve b3e218 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e218
        have b3e224 : (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b3e130
             have i₂ := b3e219
             grind)
          | exact superpose b3e219 b3e130
          | exact resolve b3e130 b3e219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e130 b3e219
        have b3e229 : False := by grind
        exact b3e229
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b4e22 : (M.op y x) = (M.op x x) := by grind
          have b4e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e23
            | exact resolve b4e23 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (M.op y y) ≠ (M.op x x) := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e21
            | exact resolve b4e21 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e27 X0 X1
               grind)
            | exact superpose b4e27 b4e14
            | exact resolve b4e14 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e28 X1 X0
               grind)
            | exact superpose b4e28 b4e14
            | exact resolve b4e14 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e32
            | exact resolve b4e32 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e65 (σ X0)
               grind)
            | exact superpose b4e65 b4e19
            | exact resolve b4e19 b4e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b4e28 X0 (τ X0)
               have i₂ := b4e65 (τ X0)
               grind)
            | exact superpose b4e65 b4e28
            | exact resolve b4e28 b4e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e73 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e70 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e70
            | exact resolve b4e70 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e67 X0
               have i₂ := b4e65 X0
               grind)
            | exact superpose b4e65 b4e67
            | exact resolve b4e67 b4e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67
          have b4e79 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e73 X0
               have i₂ := b4e65 X0
               grind)
            | exact superpose b4e65 b4e73
            | exact resolve b4e73 b4e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e65 b4e73
          have b4e100 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e16 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X0 X0
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e107 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e117 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
          have b4e122 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e125 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e107 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e107
          have b4e127 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e100 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e100
          have b4e130 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e117 X0 X1
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e117
            | (have j0 := b4e117 X0 X1
               grind)
            | exact resolve b4e117 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e117
          have b4e134 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e125 X0 X1
               have j1 := b4e122 X1 X0
               grind)
            | (have r₁ := b4e125 X0 X1
               have r₂ := b4e122 X0 X1
               grind)
            | (have r₁ := b4e125 X1 X0
               have r₂ := b4e122 X0 X1
               grind)
            | (have r₁ := b4e125 X0 X0
               have r₂ := b4e122 X0 X0
               grind)
            | exact resolve b4e125 b4e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e122 b4e125
          have b4e138 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e130 X0 X1
               have i₂ := b4e76 X1
               grind)
            | exact superpose b4e76 b4e130
            | (have j0 := b4e130 X0 X1
               grind)
            | exact resolve b4e130 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130
          have b4e145 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e76 y
               grind)
            | exact superpose b4e76 b4e25
            | exact resolve b4e25 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e150 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 (σ X0) X1
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e17
            | (have j0 := b4e17 (σ X0) X1
               grind)
            | exact resolve b4e17 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e151 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 (σ X0)
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e16
            | (have j0 := b4e16 X1 (σ X0)
               grind)
            | exact resolve b4e16 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e154 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e145
               have i₂ := b4e76 x
               grind)
            | exact superpose b4e76 b4e145
            | exact resolve b4e145 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e145
          have b4e172 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e14 (M.op (τ X0) (τ X0))
               have i₂ := b4e79 X0
               grind)
            | exact superpose b4e79 b4e14
            | exact resolve b4e14 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e222 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 (τ X0)
               have i₂ := b4e172 X0
               grind)
            | exact superpose b4e172 b4e16
            | (have j0 := b4e16 X1 (τ X0)
               grind)
            | exact resolve b4e16 b4e172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e301 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X0 X0) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e28 X1 X0
               have i₂ := b4e127 (τ X1) X0
               grind)
            | exact superpose b4e127 b4e28
            | (have j1 := b4e127 (τ X1) X0
               grind)
            | exact resolve b4e28 b4e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e127
          have b4e447 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e28 X0 X1
               have i₂ := b4e134 X1 (τ X0)
               grind)
            | exact superpose b4e134 b4e28
            | (have j1 := b4e134 X1 (τ X0)
               grind)
            | exact resolve b4e28 b4e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e134
          have b4e485 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e447 X0 X1
               have i₂ := b4e79 X0
               grind)
            | exact superpose b4e79 b4e447
            | (have j0 := b4e447 X0 X1
               grind)
            | exact resolve b4e447 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e447
          have b4e513 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e485 X0 X1
               have i₂ := b4e172 X0
               grind)
            | exact superpose b4e172 b4e485
            | (have j0 := b4e485 X0 X1
               grind)
            | exact resolve b4e485 b4e172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e172 b4e485
          have b4e1641 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (σ X0) (σ X1)
               have i₂ := b4e138 X1 X0
               grind)
            | exact superpose b4e138 b4e16
            | (have j0 := b4e16 (σ X0) (σ X1)
               have j1 := b4e138 X1 X0
               grind)
            | exact resolve b4e16 b4e138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1659 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e138 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e138
          have b4e1709 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e1641 X0 X1
               have j1 := b4e151 X1 (σ X0)
               grind)
            | (have r₁ := b4e1641 X0 X0
               have r₂ := b4e151 X0 (σ X0)
               grind)
            | (have r₁ := b4e1641 X0 X0
               have r₂ := b4e151 X0 (σ X0)
               grind)
            | exact resolve b4e1641 b4e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e151 b4e1641
          have b4e1763 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1709 X0 X1
               have i₂ := b4e76 X1
               grind)
            | exact superpose b4e76 b4e1709
            | (have j0 := b4e1709 X0 X1
               grind)
            | exact resolve b4e1709 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1709
          have b4e1799 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1763 X0 X1
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e1763
            | (have j0 := b4e1763 X0 X1
               grind)
            | exact resolve b4e1763 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1763
          have b4e1821 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1799 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e1799
            | (have j0 := b4e1799 X0 X1
               grind)
            | exact resolve b4e1799 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1799
          have b4e6980 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (k X0 (τ (σ X1))) = (M.op (τ (σ X1)) X0) ∨ (M.op X0 X0) = (M.op (τ (σ X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e301 X0 (σ X1)
               grind)
            | exact superpose b4e301 b4e19
            | (have j1 := b4e301 X0 (σ X1)
               grind)
            | exact resolve b4e19 b4e301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e301
          have b4e7091 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (τ (σ X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e6980 X0 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e6980
            | (have j0 := b4e6980 X0 X1
               grind)
            | exact resolve b4e6980 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6980
          have b4e7137 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e7091 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e7091
            | (have j0 := b4e7091 X0 X1
               grind)
            | exact resolve b4e7091 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7091
          have b4e10246 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e222 X0 X1
               have i₂ := b4e513 X0 X1
               grind)
            | exact superpose b4e513 b4e222
            | (have j0 := b4e222 X0 X1
               have j1 := b4e513 X0 X1
               grind)
            | (have r₁ := b4e222 X0 X1
               have r₂ := b4e513 X0 X1
               grind)
            | exact resolve b4e222 b4e513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e222
          have b4e10291 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e15 (M.op X0 X0)
               have i₂ := b4e513 X0 X1
               grind)
            | exact superpose b4e513 b4e15
            | (have j1 := b4e513 X0 X1
               grind)
            | exact resolve b4e15 b4e513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e513
          have b4e10460 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b4e10246 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10246
          have b4e16641 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e1821 (τ X1) (τ X0)
               have i₂ := b4e45 X0 X1
               grind)
            | exact superpose b4e45 b4e1821
            | (have j0 := b4e1821 (τ X0) (τ X1)
               grind)
            | exact resolve b4e1821 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1821
          have b4e16750 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e16641 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e16641
            | (have j0 := b4e16641 X0 X1
               grind)
            | exact resolve b4e16641 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16641
          have b4e16788 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e16750 X0 X1
               have i₂ := b4e79 X1
               grind)
            | exact superpose b4e79 b4e16750
            | (have j0 := b4e16750 X0 X1
               grind)
            | exact resolve b4e16750 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16750
          have b4e16822 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e16788 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e16788
            | (have j0 := b4e16788 X0 X1
               grind)
            | exact resolve b4e16788 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16788
          have b4e16846 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e16822 X0 X1
               have i₂ := b4e79 X0
               grind)
            | exact superpose b4e79 b4e16822
            | (have j0 := b4e16822 X0 X1
               grind)
            | exact resolve b4e16822 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16822
          have b4e16864 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16846 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e16846
            | (have j0 := b4e16846 X0 X1
               grind)
            | exact resolve b4e16846 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16846
          have b4e16877 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16864 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e16864
            | (have j0 := b4e16864 X0 X1
               grind)
            | exact resolve b4e16864 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16864
          have b4e16886 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e16877 X0 X1
               have i₂ := b4e79 X0
               grind)
            | exact superpose b4e79 b4e16877
            | (have j0 := b4e16877 X0 X1
               grind)
            | exact resolve b4e16877 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16877
          have b4e80236 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (τ X1)) (σ X0)) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e1659 (τ X1) X0
               have i₂ := b4e10460 X1 X0
               grind)
            | exact superpose b4e10460 b4e1659
            | (have j0 := b4e1659 (τ X1) X0
               have j1 := b4e10460 X1 X0
               grind)
            | exact resolve b4e1659 b4e10460
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1659
          have b4e80280 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e27 X0 (τ X1)
               have i₂ := b4e10460 X1 (τ X0)
               grind)
            | exact superpose b4e10460 b4e27
            | (have j1 := b4e10460 X1 (τ X0)
               grind)
            | exact resolve b4e27 b4e10460
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e80662 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 (σ X1) X0
               have i₂ := b4e10460 (σ X0) X1
               grind)
            | exact superpose b4e10460 b4e32
            | (have j1 := b4e10460 (σ X0) X1
               grind)
            | exact resolve b4e32 b4e10460
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10460
          have b4e80766 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (τ X1)) (σ X0)) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have j0 := b4e80236 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80236
          have b4e80884 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e80662 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e80662
            | (have j0 := b4e80662 X0 X1
               grind)
            | exact resolve b4e80662 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80662
          have b4e81055 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e80280 X0 X1
               have i₂ := b4e79 X0
               grind)
            | exact superpose b4e79 b4e80280
            | (have j0 := b4e80280 X0 X1
               grind)
            | exact resolve b4e80280 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80280
          have b4e81090 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e80766 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e80766
            | (have j0 := b4e80766 X0 X1
               grind)
            | exact resolve b4e80766 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80766
          have b4e81335 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e80884 X0 X1
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e80884
            | (have j0 := b4e80884 X0 X1
               grind)
            | exact resolve b4e80884 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80884
          have b4e81421 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e81055 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e81055
            | (have j0 := b4e81055 X0 X1
               grind)
            | exact resolve b4e81055 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81055
          have b4e81454 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e81090 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e81090
            | (have j0 := b4e81090 X0 X1
               grind)
            | exact resolve b4e81090 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81090
          have b4e81589 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e81335 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e81335
            | (have j0 := b4e81335 X0 X1
               grind)
            | exact resolve b4e81335 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81335
          have b4e81653 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e81421 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e81421
            | (have j0 := b4e81421 X0 X1
               grind)
            | exact resolve b4e81421 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81421
          have b4e81678 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e81454 X0 X1
               have i₂ := b4e79 X1
               grind)
            | exact superpose b4e79 b4e81454
            | (have j0 := b4e81454 X0 X1
               grind)
            | exact resolve b4e81454 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e79 b4e81454
          have b4e81754 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e81589 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e81589
            | (have j0 := b4e81589 X0 X1
               grind)
            | exact resolve b4e81589 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81589
          have b4e81806 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e81653 X0 X1
               have i₂ := b4e45 X1 X0
               grind)
            | exact superpose b4e45 b4e81653
            | (have j0 := b4e81653 X0 X1
               grind)
            | exact resolve b4e81653 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45 b4e81653
          have b4e81807 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have j0 := b4e81678 X0 X1
               have j1 := b4e150 X0 X1
               grind)
            | (have r₁ := b4e81678 X0 X1
               have r₂ := b4e150 X0 X1
               grind)
            | exact resolve b4e81678 b4e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e150 b4e81678
          have b4e81854 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e81754 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e81754
            | (have j0 := b4e81754 X0 X1
               grind)
            | exact resolve b4e81754 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81754
          have b4e83375 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X1 X0
               have i₂ := b4e81854 (σ X0) X1
               grind)
            | exact superpose b4e81854 b4e32
            | (have j1 := b4e81854 (σ X0) X1
               grind)
            | exact resolve b4e32 b4e81854
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81854
          have b4e83842 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e83375 X0 X1
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e83375
            | (have j0 := b4e83375 X0 X1
               grind)
            | exact resolve b4e83375 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83375
          have b4e84485 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e83842 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e83842
            | (have j0 := b4e83842 X0 X1
               grind)
            | exact resolve b4e83842 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83842
          have b4e89130 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e16886 X0 X1
               have i₂ := b4e81806 X0 X1
               grind)
            | exact superpose b4e81806 b4e16886
            | (have j0 := b4e16886 X1 X0
               have j1 := b4e81806 X1 X0
               grind)
            | (have r₁ := b4e16886 X0 X1
               have r₂ := b4e81806 X0 X1
               grind)
            | (have r₁ := b4e16886 X1 X1
               have r₂ := b4e81806 X1 X1
               grind)
            | exact resolve b4e16886 b4e81806
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e89244 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e81806 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81806
          have b4e89259 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e89130 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89130
          have b4e89363 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e89259 X0 X1
               have j1 := b4e89244 X1 X0
               grind)
            | (have r₁ := b4e89259 X0 X1
               have r₂ := b4e89244 X0 X1
               grind)
            | (have r₁ := b4e89259 X1 X0
               have r₂ := b4e89244 X0 X1
               grind)
            | (have r₁ := b4e89259 X0 X0
               have r₂ := b4e89244 X0 X0
               grind)
            | exact resolve b4e89259 b4e89244
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89244 b4e89259
          have b4e103200 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (M.op X0 (τ X1)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e89363 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e89363
            | (have j0 := b4e89363 (σ X0) X1
               grind)
            | exact resolve b4e89363 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89363
          have b4e103265 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op X0 (τ X1)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e103200 X0 X1
               have i₂ := b4e32 X1 X0
               grind)
            | exact superpose b4e32 b4e103200
            | (have j0 := b4e103200 X0 X1
               grind)
            | exact resolve b4e103200 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32 b4e103200
          have b4e123309 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e81807 X0 (σ X0)
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e81807
            | (have j0 := b4e81807 X1 (σ X0)
               grind)
            | exact resolve b4e81807 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81807
          have b4e123353 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e123309 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e123309
            | (have j0 := b4e123309 X0 X1
               grind)
            | exact resolve b4e123309 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e123309
          have b4e123361 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e123353 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e123353
            | (have j0 := b4e123353 X0 X1
               grind)
            | exact resolve b4e123353 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e123353
          have b4e142420 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e41 X0 (σ X1)
               have i₂ := b4e84485 X1 (σ X0)
               grind)
            | exact superpose b4e84485 b4e41
            | (have j1 := b4e84485 X1 (σ X0)
               grind)
            | exact resolve b4e41 b4e84485
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84485
          have b4e142477 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e142420 X0 X1
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e142420
            | (have j0 := b4e142420 X0 X1
               grind)
            | exact resolve b4e142420 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142420
          have b4e142504 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e142477 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e142477
            | (have j0 := b4e142477 X0 X1
               grind)
            | exact resolve b4e142477 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142477
          have b4e142521 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e142504 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e142504
            | (have j0 := b4e142504 X0 X1
               grind)
            | exact resolve b4e142504 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142504
          have b4e142534 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e142521 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e142521
            | (have j0 := b4e142521 X0 X1
               grind)
            | exact resolve b4e142521 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142521
          have b4e142539 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e142534 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e142534
            | (have j0 := b4e142534 X0 X1
               grind)
            | exact resolve b4e142534 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142534
          have b4e146818 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e142539 y x
               grind)
            | exact superpose b4e142539 b4e20
            | (have j1 := b4e142539 y x
               grind)
            | exact resolve b4e20 b4e142539
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142539
          have b4e149568 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e146818
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e146818
            | (have j1 := b4e18 y x
               grind)
            | exact resolve b4e146818 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e146818
          have b4e149586 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b4e149568
          have b4e149587 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b4e149586
          have b4e193021 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e41 X0 (σ X1)
               have i₂ := b4e103265 X1 (σ X0)
               grind)
            | exact superpose b4e103265 b4e41
            | (have j1 := b4e103265 X1 (σ X0)
               grind)
            | exact resolve b4e41 b4e103265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e103265
          have b4e193026 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e193021 X0 X1
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e193021
            | (have j0 := b4e193021 X0 X1
               grind)
            | exact resolve b4e193021 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e193021
          have b4e193044 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e193026 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e193026
            | (have j0 := b4e193026 X0 X1
               grind)
            | exact resolve b4e193026 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e193026
          have b4e193055 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e193044 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e193044
            | (have j0 := b4e193044 X0 X1
               grind)
            | exact resolve b4e193044 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e193044
          have b4e193061 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e193055 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e193055
            | (have j0 := b4e193055 X0 X1
               grind)
            | exact resolve b4e193055 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e193055
          have b4e193062 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e193061 X0 X1
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e193061
            | (have j0 := b4e193061 X0 X1
               grind)
            | exact resolve b4e193061 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e193061
          have b4e194534 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e193062 y x
               grind)
            | exact superpose b4e193062 b4e20
            | (have j1 := b4e193062 y x
               grind)
            | exact resolve b4e20 b4e193062
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e193062
          have b4e316324 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e10291 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e10291
            | (have j0 := b4e10291 (σ X0) X1
               grind)
            | exact resolve b4e10291 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10291
          have b4e316351 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e316324 X0 X1
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e316324
            | (have j0 := b4e316324 X0 X1
               grind)
            | exact resolve b4e316324 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e316324
          have b4e316355 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e316351 X0 X1
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e316351
            | (have j0 := b4e316351 X0 X1
               grind)
            | exact resolve b4e316351 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e76 b4e316351
          have b4e316359 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e316355 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e316355
            | (have j0 := b4e316355 X0 X1
               grind)
            | exact resolve b4e316355 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e316355
          have b4e609670 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e123361 x y
               grind)
            | exact superpose b4e123361 b4e20
            | (have j1 := b4e123361 x y
               grind)
            | exact resolve b4e20 b4e123361
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e123361
          have b4e609680 : (σ (M.op x x)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
            first
            | (have j1 := b4e316359 x y
               grind)
            | (have r₁ := b4e609670
               have r₂ := b4e316359 x y
               grind)
            | exact resolve b4e609670 b4e316359
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e316359 b4e609670
          have b4e611255 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e7137 y x
               have i₂ := b4e609680
               grind)
            | exact superpose b4e609680 b4e7137
            | (have j0 := b4e7137 y x
               grind)
            | exact resolve b4e7137 b4e609680
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7137
          have b4e611264 : (k y x) = (τ (σ (M.op x x))) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e609680
               grind)
            | exact superpose b4e609680 b4e14
            | exact resolve b4e14 b4e609680
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e609680
          have b4e611287 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b4e611255
          have b4e611310 : (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e611264
               have i₂ := b4e14 (M.op x x)
               grind)
            | exact superpose b4e14 b4e611264
            | exact resolve b4e611264 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e611264
          have b4e611314 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b4e611287
               have r₂ := b4e154
               grind)
            | exact resolve b4e611287 b4e154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e154 b4e611287
          have b4e613173 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k y x) := by grind
          clear b4e611310
          have b4e615900 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e16886 y x
               have i₂ := b4e611314
               grind)
            | exact superpose b4e611314 b4e16886
            | (have j0 := b4e16886 y x
               grind)
            | exact resolve b4e16886 b4e611314
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16886 b4e611314
          have b4e615918 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b4e615900
          have b4e615925 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b4e615918
               have r₂ := b4e149587
               grind)
            | exact resolve b4e615918 b4e149587
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e149587 b4e615918
          have b4e619030 : (M.op x y) ≠ (M.op x x) := by
            first
            | (have i₁ := b4e26
               have i₂ := b4e615925
               grind)
            | exact superpose b4e615925 b4e26
            | exact resolve b4e26 b4e615925
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e619032 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e194534
               have i₂ := b4e615925
               grind)
            | exact superpose b4e615925 b4e194534
            | exact resolve b4e194534 b4e615925
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e194534
          have b4e619041 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e17 y X0
               have i₂ := b4e615925
               grind)
            | exact superpose b4e615925 b4e17
            | (have j0 := b4e17 y X0
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e615925
               grind)
            | exact resolve b4e17 b4e615925
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e615925
          have b4e619271 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) := by grind
          clear b4e619032
          have b4e619272 : (M.op x y) = (k y x) := by grind
          clear b4e619271
          have b4e855438 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j0 := b4e619041 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e619041
          have b4e855439 : (M.op x x) = (k y x) := by
            first
            | (have r₁ := b4e855438
               have r₂ := b4e613173
               grind)
            | exact resolve b4e855438 b4e613173
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e613173 b4e855438
          have b4e866609 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e619272
               have i₂ := b4e855439
               grind)
            | exact superpose b4e855439 b4e619272
            | exact resolve b4e619272 b4e855439
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e619272 b4e855439
          have b4e866672 : False := by grind
          exact b4e866672
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b5e22 : (M.op y x) = (M.op x x) := by grind
          have b5e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op y y) ≠ (M.op x x) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
          have b5e74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e65 X0
               have i₂ := b5e63 X0
               grind)
            | exact superpose b5e63 b5e65
            | exact resolve b5e65 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63 b5e65
          have b5e82 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by
            first
            | (have i₁ := b5e17 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 x x
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e85 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
          clear b5e82
          have b5e86 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b5e85
               have r₂ := b5e25
               grind)
            | exact resolve b5e85 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e85
          have b5e99 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ y) (σ y)
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e136 : (M.op (σ y) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e74 y
               grind)
            | exact superpose b5e74 b5e23
            | exact resolve b5e23 b5e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e74
          have b5e1032 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e99 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e99
          have b5e1033 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1032
               have r₂ := b5e24
               grind)
            | exact resolve b5e1032 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1032
          have b5e1034 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1033
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1033
            | exact resolve b5e1033 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1033
          have b5e1035 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e1034
               have i₂ := b5e86
               grind)
            | exact superpose b5e86 b5e1034
            | exact resolve b5e1034 b5e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e86 b5e1034
          have b5e1036 : False := by grind
          exact b5e1036
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op y x) ≠ (M.op y y) := by grind
        have b6e21 : (M.op y x) ≠ (M.op x x) := by grind
        have b6e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e48 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ y) (σ y)
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
        have b6e50 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b6e48
        have b6e51 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
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
        have b6e70 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e51
             grind)
          | exact superpose b6e51 b6e15
          | exact resolve b6e15 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e72 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e70
        have b6e73 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e72
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e72
          | exact resolve b6e72 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e74 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e73
             have i₂ := b6e49 x
             grind)
          | exact superpose b6e49 b6e73
          | exact resolve b6e73 b6e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49 b6e73
        have b6e123 : (k x y) = (τ (σ (M.op x x))) := by
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
        have b6e124 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b6e123
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e123
          | exact resolve b6e123 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e123
        have b6e138 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e124
             grind)
          | exact superpose b6e124 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e124
        have b6e139 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) := by grind
        clear b6e138
        have b6e141 : (M.op y x) = (M.op y y) := by
          first
          | (have r₁ := b6e139
             have r₂ := b6e21
             grind)
          | exact resolve b6e139 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e139
        have b6e143 : False := by grind
        exact b6e143
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b7e22 : (M.op y x) ≠ (M.op x x) := by grind
          have b7e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
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
          have b7e65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
          have b7e74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e65 X0
               have i₂ := b7e63 X0
               grind)
            | exact superpose b7e63 b7e65
            | exact resolve b7e65 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63 b7e65
          have b7e83 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) (σ x)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e85 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e83
          have b7e86 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e85
               have r₂ := b7e25
               grind)
            | exact resolve b7e85 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e85
          have b7e87 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
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
          have b7e88 : (σ (k x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e87
               have i₂ := b7e74 y
               grind)
            | exact superpose b7e74 b7e87
            | exact resolve b7e87 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74 b7e87
          have b7e93 : (k x y) = (τ (σ (M.op y y))) := by
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
          have b7e94 : (M.op y y) = (k x y) := by
            first
            | (have i₁ := b7e93
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e93
            | exact resolve b7e93 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93
          have b7e145 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
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
          have b7e146 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by grind
          clear b7e145
          have b7e148 : (M.op y x) = (M.op x x) := by
            first
            | (have r₁ := b7e146
               have r₂ := b7e21
               grind)
            | exact resolve b7e146 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e146
          have b7e150 : False := by grind
          exact b7e150
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b8e41 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          have b8e61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e61 (σ X0)
               grind)
            | exact superpose b8e61 b8e19
            | exact resolve b8e19 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e66 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 (τ X0)
               have i₂ := b8e61 (τ X0)
               grind)
            | exact superpose b8e61 b8e26
            | exact resolve b8e26 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e69 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e66 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e66
            | exact resolve b8e66 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e63 X0
               have i₂ := b8e61 X0
               grind)
            | exact superpose b8e61 b8e63
            | exact resolve b8e63 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e75 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e69 X0
               have i₂ := b8e61 X0
               grind)
            | exact superpose b8e61 b8e69
            | exact resolve b8e69 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61 b8e69
          have b8e89 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 (σ X0)
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e16
            | (have j0 := b8e16 X1 (σ X0)
               grind)
            | exact resolve b8e16 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e107 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e116 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
          have b8e122 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e124 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e107 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107
          have b8e129 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e116 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e116
            | (have j0 := b8e116 X0 X1
               grind)
            | exact resolve b8e116 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e116
          have b8e131 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e124 X0 X1
               have j1 := b8e122 X1 X0
               grind)
            | (have r₁ := b8e124 X0 X1
               have r₂ := b8e122 X0 X1
               grind)
            | (have r₁ := b8e124 X1 X0
               have r₂ := b8e122 X0 X1
               grind)
            | (have r₁ := b8e124 X0 X0
               have r₂ := b8e122 X0 X0
               grind)
            | exact resolve b8e124 b8e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e122 b8e124
          have b8e134 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e129 X0 X1
               have i₂ := b8e72 X1
               grind)
            | exact superpose b8e72 b8e129
            | (have j0 := b8e129 X0 X1
               grind)
            | exact resolve b8e129 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e129
          have b8e146 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e14
            | exact resolve b8e14 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e199 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 (τ X0)
               have i₂ := b8e146 X0
               grind)
            | exact superpose b8e146 b8e16
            | (have j0 := b8e16 X1 (τ X0)
               grind)
            | exact resolve b8e16 b8e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e372 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e131 X1 (τ X0)
               grind)
            | exact superpose b8e131 b8e26
            | (have j1 := b8e131 X1 (τ X0)
               grind)
            | exact resolve b8e26 b8e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e131
          have b8e396 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e372 X0 X1
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e372
            | (have j0 := b8e372 X0 X1
               grind)
            | exact resolve b8e372 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e372
          have b8e418 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e396 X0 X1
               have i₂ := b8e146 X0
               grind)
            | exact superpose b8e146 b8e396
            | (have j0 := b8e396 X0 X1
               grind)
            | exact resolve b8e396 b8e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e146 b8e396
          have b8e1365 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X0) (σ X1)
               have i₂ := b8e134 X1 X0
               grind)
            | exact superpose b8e134 b8e16
            | (have j0 := b8e16 (σ X0) (σ X1)
               have j1 := b8e134 X1 X0
               grind)
            | exact resolve b8e16 b8e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e134
          have b8e1429 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e1365 X0 X1
               have j1 := b8e89 X1 (σ X0)
               grind)
            | (have r₁ := b8e1365 X0 X0
               have r₂ := b8e89 X0 (σ X0)
               grind)
            | (have r₁ := b8e1365 X0 X0
               have r₂ := b8e89 X0 (σ X0)
               grind)
            | exact resolve b8e1365 b8e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89 b8e1365
          have b8e1483 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1429 X0 X1
               have i₂ := b8e72 X1
               grind)
            | exact superpose b8e72 b8e1429
            | (have j0 := b8e1429 X0 X1
               grind)
            | exact resolve b8e1429 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1429
          have b8e1519 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1483 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e1483
            | (have j0 := b8e1483 X0 X1
               grind)
            | exact resolve b8e1483 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1483
          have b8e1541 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1519 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e1519
            | (have j0 := b8e1519 X0 X1
               grind)
            | exact resolve b8e1519 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1519
          have b8e7511 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e199 X0 X1
               have i₂ := b8e418 X0 X1
               grind)
            | exact superpose b8e418 b8e199
            | (have j0 := b8e199 X0 X1
               have j1 := b8e418 X0 X1
               grind)
            | (have r₁ := b8e199 X0 X1
               have r₂ := b8e418 X0 X1
               grind)
            | exact resolve b8e199 b8e418
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e199 b8e418
          have b8e7684 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b8e7511 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7511
          have b8e12874 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1541 (τ X1) (τ X0)
               have i₂ := b8e41 X0 X1
               grind)
            | exact superpose b8e41 b8e1541
            | (have j0 := b8e1541 (τ X0) (τ X1)
               grind)
            | exact resolve b8e1541 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1541
          have b8e12965 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e12874 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e12874
            | (have j0 := b8e12874 X0 X1
               grind)
            | exact resolve b8e12874 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e12874
          have b8e12995 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e12965 X0 X1
               have i₂ := b8e75 X1
               grind)
            | exact superpose b8e75 b8e12965
            | (have j0 := b8e12965 X0 X1
               grind)
            | exact resolve b8e12965 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e12965
          have b8e13021 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e12995 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e12995
            | (have j0 := b8e12995 X0 X1
               grind)
            | exact resolve b8e12995 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e12995
          have b8e13037 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13021 X0 X1
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e13021
            | (have j0 := b8e13021 X0 X1
               grind)
            | exact resolve b8e13021 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13021
          have b8e13047 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13037 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e13037
            | (have j0 := b8e13037 X0 X1
               grind)
            | exact resolve b8e13037 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13037
          have b8e13052 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13047 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e13047
            | (have j0 := b8e13047 X0 X1
               grind)
            | exact resolve b8e13047 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13047
          have b8e13053 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e13052 X0 X1
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e13052
            | (have j0 := b8e13052 X0 X1
               grind)
            | exact resolve b8e13052 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13052
          have b8e89416 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X0 (τ X1)
               have i₂ := b8e7684 X1 (τ X0)
               grind)
            | exact superpose b8e7684 b8e25
            | (have j1 := b8e7684 X1 (τ X0)
               grind)
            | exact resolve b8e25 b8e7684
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25
          have b8e89465 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 (σ X1) X0
               have i₂ := b8e7684 (σ X0) X1
               grind)
            | exact superpose b8e7684 b8e30
            | (have j1 := b8e7684 (σ X0) X1
               grind)
            | exact resolve b8e30 b8e7684
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7684
          have b8e89475 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e89465 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e89465
            | (have j0 := b8e89465 X0 X1
               grind)
            | exact resolve b8e89465 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89465
          have b8e89488 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e89416 X0 X1
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e89416
            | (have j0 := b8e89416 X0 X1
               grind)
            | exact resolve b8e89416 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75 b8e89416
          have b8e89514 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e89475 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e89475
            | (have j0 := b8e89475 X0 X1
               grind)
            | exact resolve b8e89475 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89475
          have b8e89519 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e89488 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e89488
            | (have j0 := b8e89488 X0 X1
               grind)
            | exact resolve b8e89488 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89488
          have b8e89536 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e89514 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e89514
            | (have j0 := b8e89514 X0 X1
               grind)
            | exact resolve b8e89514 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89514
          have b8e89541 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e89519 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e89519
            | (have j0 := b8e89519 X0 X1
               grind)
            | exact resolve b8e89519 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89519
          have b8e89551 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e89536 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e89536
            | (have j0 := b8e89536 X0 X1
               grind)
            | exact resolve b8e89536 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89536
          have b8e89554 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e89541 X0 X1
               have i₂ := b8e41 X1 X0
               grind)
            | exact superpose b8e41 b8e89541
            | (have j0 := b8e89541 X0 X1
               grind)
            | exact resolve b8e89541 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41 b8e89541
          have b8e89558 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e89551 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e89551
            | (have j0 := b8e89551 X0 X1
               grind)
            | exact resolve b8e89551 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89551
          have b8e90225 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X1 X0
               have i₂ := b8e89558 (σ X0) X1
               grind)
            | exact superpose b8e89558 b8e30
            | (have j1 := b8e89558 (σ X0) X1
               grind)
            | exact resolve b8e30 b8e89558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89558
          have b8e90336 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e90225 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e90225
            | (have j0 := b8e90225 X0 X1
               grind)
            | exact resolve b8e90225 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90225
          have b8e90475 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e90336 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e90336
            | (have j0 := b8e90336 X0 X1
               grind)
            | exact resolve b8e90336 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90336
          have b8e98236 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e89554 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e89554
            | (have j1 := b8e18 X1 X0
               grind)
            | exact resolve b8e89554 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e98367 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e13053 X0 X1
               have i₂ := b8e89554 X0 X1
               grind)
            | exact superpose b8e89554 b8e13053
            | (have j0 := b8e13053 X1 X0
               have j1 := b8e89554 X1 X0
               grind)
            | (have r₁ := b8e13053 X0 X1
               have r₂ := b8e89554 X0 X1
               grind)
            | (have r₁ := b8e13053 X1 X1
               have r₂ := b8e89554 X1 X1
               grind)
            | exact resolve b8e13053 b8e89554
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13053
          have b8e98481 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e89554 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89554
          have b8e98496 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e98367 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98367
          have b8e98544 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e98236 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98236
          have b8e98606 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e98496 X0 X1
               have j1 := b8e98481 X1 X0
               grind)
            | (have r₁ := b8e98496 X0 X1
               have r₂ := b8e98481 X0 X1
               grind)
            | (have r₁ := b8e98496 X1 X0
               have r₂ := b8e98481 X0 X1
               grind)
            | (have r₁ := b8e98496 X0 X0
               have r₂ := b8e98481 X0 X0
               grind)
            | exact resolve b8e98496 b8e98481
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98481 b8e98496
          have b8e102950 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X1 X0
               have i₂ := b8e98544 X0 X1
               grind)
            | (have i₁ := b8e17 X1 X1
               have i₂ := b8e98544 X0 X1
               grind)
            | exact superpose b8e98544 b8e17
            | (have j0 := b8e17 X0 X1
               have j1 := b8e98544 X1 X0
               grind)
            | (have r₁ := b8e17 X1 X0
               have r₂ := b8e98544 X0 X1
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e98544 X0 X0
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e98544 X1 X1
               grind)
            | exact resolve b8e17 b8e98544
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e103052 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (M.op (σ X0) X1) ∨ (τ (M.op (σ X0) X1)) = (M.op (τ (σ X0)) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e72 X0
               have i₂ := b8e98544 (σ X0) X1
               grind)
            | (have i₁ := b8e72 X0
               have i₂ := b8e98544 (σ X0) (σ X0)
               grind)
            | exact superpose b8e98544 b8e72
            | (have j1 := b8e98544 (σ X0) X1
               grind)
            | exact resolve b8e72 b8e98544
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e103057 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e98544 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98544
          have b8e103073 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e102950 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102950
          have b8e103076 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e103052 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e103052
            | (have j0 := b8e103052 X0 X1
               grind)
            | exact resolve b8e103052 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e103052
          have b8e103096 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e103073 X0 X1
               have j1 := b8e103057 X1 X0
               grind)
            | (have r₁ := b8e103073 X0 X1
               have r₂ := b8e103057 X0 X1
               grind)
            | (have r₁ := b8e103073 X1 X0
               have r₂ := b8e103057 X0 X1
               grind)
            | (have r₁ := b8e103073 X0 X0
               have r₂ := b8e103057 X0 X0
               grind)
            | exact resolve b8e103073 b8e103057
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e103057 b8e103073
          have b8e117377 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e98606 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e98606
            | (have j0 := b8e98606 (σ X0) X1
               grind)
            | exact resolve b8e98606 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98606
          have b8e117442 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e117377 X0 X1
               have i₂ := b8e30 X1 X0
               grind)
            | exact superpose b8e30 b8e117377
            | (have j0 := b8e117377 X0 X1
               grind)
            | exact resolve b8e117377 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e117377
          have b8e121829 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (τ (M.op (σ X0) X1)) = (M.op (τ (σ X0)) (τ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X1 X0
               have i₂ := b8e103096 X1 (σ X0)
               grind)
            | exact superpose b8e103096 b8e30
            | (have j1 := b8e103096 X1 (σ X0)
               grind)
            | exact resolve b8e30 b8e103096
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e103096
          have b8e121853 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (τ (M.op (σ X0) X1)) = (M.op (τ (σ X0)) (τ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e121829 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e121829
            | (have j0 := b8e121829 X0 X1
               grind)
            | exact resolve b8e121829 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121829
          have b8e121867 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ X1) X0) ∨ (τ (M.op (σ X0) X1)) = (M.op (τ (σ X0)) (τ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e121853 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e121853
            | (have j0 := b8e121853 X0 X1
               grind)
            | exact resolve b8e121853 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121853
          have b8e121876 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e121867 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e121867
            | (have j0 := b8e121867 X0 X1
               grind)
            | exact resolve b8e121867 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121867
          have b8e121880 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X0 X0) = (k (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e121876 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e121876
            | (have j0 := b8e121876 X0 X1
               grind)
            | exact resolve b8e121876 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121876
          have b8e158616 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e38 X0 (σ X1)
               have i₂ := b8e90475 X1 (σ X0)
               grind)
            | exact superpose b8e90475 b8e38
            | (have j1 := b8e90475 X1 (σ X0)
               grind)
            | exact resolve b8e38 b8e90475
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90475
          have b8e158673 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e158616 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e158616
            | (have j0 := b8e158616 X0 X1
               grind)
            | exact resolve b8e158616 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158616
          have b8e158700 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e158673 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e158673
            | (have j0 := b8e158673 X0 X1
               grind)
            | exact resolve b8e158673 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158673
          have b8e158717 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e158700 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e158700
            | (have j0 := b8e158700 X0 X1
               grind)
            | exact resolve b8e158700 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158700
          have b8e158730 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e158717 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e158717
            | (have j0 := b8e158717 X0 X1
               grind)
            | exact resolve b8e158717 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158717
          have b8e158735 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e158730 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e158730
            | (have j0 := b8e158730 X0 X1
               grind)
            | exact resolve b8e158730 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158730
          have b8e159573 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e158735 y x
               grind)
            | exact superpose b8e158735 b8e20
            | (have j1 := b8e158735 y x
               grind)
            | exact resolve b8e20 b8e158735
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158735
          have b8e159916 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e159573
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e159573
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e159573 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e159573
          have b8e159934 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e159916
          have b8e159935 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e159934
          have b8e160667 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) ∨ (M.op x y) = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b8e17 y X0
               have i₂ := b8e159935
               grind)
            | exact superpose b8e159935 b8e17
            | (have j0 := b8e17 y X0
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e159935
               grind)
            | exact resolve b8e17 b8e159935
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e231016 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e38 X0 (σ X1)
               have i₂ := b8e117442 X1 (σ X0)
               grind)
            | exact superpose b8e117442 b8e38
            | (have j1 := b8e117442 X1 (σ X0)
               grind)
            | exact resolve b8e38 b8e117442
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38 b8e117442
          have b8e231021 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e231016 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e231016
            | (have j0 := b8e231016 X0 X1
               grind)
            | exact resolve b8e231016 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e231016
          have b8e231039 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e231021 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e231021
            | (have j0 := b8e231021 X0 X1
               grind)
            | exact resolve b8e231021 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e231021
          have b8e231050 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e231039 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e231039
            | (have j0 := b8e231039 X0 X1
               grind)
            | exact resolve b8e231039 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e231039
          have b8e231056 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e231050 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e231050
            | (have j0 := b8e231050 X0 X1
               grind)
            | exact resolve b8e231050 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e231050
          have b8e231057 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e231056 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e231056
            | (have j0 := b8e231056 X0 X1
               grind)
            | exact resolve b8e231056 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e231056
          have b8e238733 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e231057 y x
               grind)
            | exact superpose b8e231057 b8e20
            | (have j1 := b8e231057 y x
               grind)
            | exact resolve b8e20 b8e231057
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e231057
          have b8e242555 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e238733
               have i₂ := b8e159935
               grind)
            | exact superpose b8e159935 b8e238733
            | exact resolve b8e238733 b8e159935
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e159935 b8e238733
          have b8e242558 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e242555
          have b8e242559 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e242558
          have b8e2707943 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op (σ X0) X1)) ∨ (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (M.op X0 X0)
               have i₂ := b8e103076 X0 X1
               grind)
            | exact superpose b8e103076 b8e14
            | (have j1 := b8e103076 X0 X1
               grind)
            | exact resolve b8e14 b8e103076
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e103076
          have b8e2708410 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e121880 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e121880
            | (have j0 := b8e121880 X1 (σ X0)
               grind)
            | exact resolve b8e121880 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121880
          have b8e2708776 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b8e2707943 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2707943
          have b8e2708785 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e2708776 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e2708776
            | (have j0 := b8e2708776 X1 (σ X0)
               grind)
            | exact resolve b8e2708776 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2708776
          have b8e2708788 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (τ (M.op (σ X1) (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e2708785 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e2708785
            | (have j0 := b8e2708785 X0 X1
               grind)
            | exact resolve b8e2708785 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72 b8e2708785
          have b8e2709473 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e15 (M.op (σ X0) (σ X1))
               have i₂ := b8e2708410 X1 X0
               grind)
            | exact superpose b8e2708410 b8e15
            | (have j1 := b8e2708410 X1 X0
               grind)
            | exact resolve b8e15 b8e2708410
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2708410
          have b8e2709898 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2709473 x y
               grind)
            | exact superpose b8e2709473 b8e20
            | (have j1 := b8e2709473 x y
               grind)
            | (have r₁ := b8e20
               have r₂ := b8e2709473 x y
               grind)
            | exact resolve b8e20 b8e2709473
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2709473
          have b8e2709901 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by grind
          clear b8e2709898
          have b8e2709910 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2709901
               grind)
            | exact superpose b8e2709901 b8e20
            | exact resolve b8e20 b8e2709901
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2709901
          have b8e2711890 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have j0 := b8e160667 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160667
          have b8e2711891 : (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e2711890
          have b8e2711902 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e242559
               have i₂ := b8e2711891
               grind)
            | exact superpose b8e2711891 b8e242559
            | exact resolve b8e242559 b8e2711891
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e242559 b8e2711891
          have b8e2711949 : (M.op x y) = (M.op x x) := by grind
          clear b8e2711902
          have b8e2711961 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e2709910
               have i₂ := b8e2711949
               grind)
            | exact superpose b8e2711949 b8e2709910
            | exact resolve b8e2709910 b8e2711949
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2709910
          have b8e2711963 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e2711949
               grind)
            | exact superpose b8e2711949 b8e16
            | (have j0 := b8e16 x x
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e2711949
               grind)
            | exact resolve b8e16 b8e2711949
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2712006 : (M.op x x) ≠ (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x x) = (τ (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b8e2708788 y x
               have i₂ := b8e2711949
               grind)
            | exact superpose b8e2711949 b8e2708788
            | (have j0 := b8e2708788 x x
               grind)
            | (have r₁ := b8e2708788 y x
               have r₂ := b8e2711949
               grind)
            | exact resolve b8e2708788 b8e2711949
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2708788
          have b8e2712023 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
          clear b8e2712006
          have b8e2712046 : (M.op y y) = (k y x) := by grind
          clear b8e2711963
          have b8e2712047 : (M.op x x) = (k y x) := by grind
          clear b8e2711961
          have b8e2712552 : (M.op y y) = (M.op x x) := by
            first
            | (have i₁ := b8e2712046
               have i₂ := b8e2712047
               grind)
            | exact superpose b8e2712047 b8e2712046
            | exact resolve b8e2712046 b8e2712047
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2712046 b8e2712047
          have b8e2714098 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e15 (M.op (σ x) (σ y))
               have i₂ := b8e2712023
               grind)
            | exact superpose b8e2712023 b8e15
            | exact resolve b8e15 b8e2712023
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2712023
          have b8e2714099 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e2714098
               have i₂ := b8e2712552
               grind)
            | exact superpose b8e2712552 b8e2714098
            | exact resolve b8e2714098 b8e2712552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2712552 b8e2714098
          have b8e2714100 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
          clear b8e2714099
          have b8e2714109 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2714100
               grind)
            | exact superpose b8e2714100 b8e20
            | exact resolve b8e20 b8e2714100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2714100
          have b8e2714128 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e2714109
               have i₂ := b8e2711949
               grind)
            | exact superpose b8e2711949 b8e2714109
            | exact resolve b8e2714109 b8e2711949
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2711949 b8e2714109
          have b8e2714129 : False := by grind
          exact b8e2714129

/-- `Equation3055`: `x = (((x ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pxx_pyy_pyx_Equation3055 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3055 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3055.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
      have b0e26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
      have b0e32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e37 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e37 (σ X0)
           grind)
        | exact superpose b0e37 b0e17
        | exact resolve b0e17 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
        intro X0
        first
        | (have i₁ := b0e22 X0 (τ X0)
           have i₂ := b0e37 (τ X0)
           grind)
        | exact superpose b0e37 b0e22
        | exact resolve b0e22 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e45 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e45
        | exact resolve b0e45 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e48 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e43 X0
           have i₂ := b0e37 X0
           grind)
        | exact superpose b0e37 b0e43
        | exact resolve b0e43 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e50 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e46 X0
           have i₂ := b0e37 X0
           grind)
        | exact superpose b0e37 b0e46
        | exact resolve b0e46 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e46
      have b0e60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 X0
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e14 X1 X1
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X0
           have j1 := b0e16 X1 X0
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | (have r₁ := b0e14 X1 X1
           have r₂ := b0e16 X1 X1
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e72 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X0 X0
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e15 X0 X1
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e15
        | (have j0 := b0e15 X0 X1
           have j1 := b0e16 X0 X1
           grind)
        | (have r₁ := b0e15 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | (have r₁ := b0e15 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | exact resolve b0e15 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e75 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e22 X0 X1
           have i₂ := b0e16 X1 (τ X0)
           grind)
        | exact superpose b0e16 b0e22
        | (have j1 := b0e16 X1 (τ X0)
           grind)
        | exact resolve b0e22 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e76 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
      have b0e80 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e16 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e82 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e72 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72
      have b0e85 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e60 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60
      have b0e87 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e76 X0 X1
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e76
        | (have j0 := b0e76 X0 X1
           grind)
        | exact resolve b0e76 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76
      have b0e89 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e82 X0 X1
           have j1 := b0e80 X1 X0
           grind)
        | (have r₁ := b0e82 X0 X1
           have r₂ := b0e80 X0 X1
           grind)
        | (have r₁ := b0e82 X1 X0
           have r₂ := b0e80 X0 X1
           grind)
        | (have r₁ := b0e82 X1 X1
           have r₂ := b0e80 X1 X1
           grind)
        | exact resolve b0e82 b0e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e80 b0e82
      have b0e93 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e87 X0 X1
           have i₂ := b0e48 X1
           grind)
        | exact superpose b0e48 b0e87
        | (have j0 := b0e87 X0 X1
           grind)
        | exact resolve b0e87 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87
      have b0e112 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e26 X1 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e26
        | exact resolve b0e26 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e179 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e21 X0 X1
           have i₂ := b0e85 X1 (τ X0)
           grind)
        | exact superpose b0e85 b0e21
        | (have j1 := b0e85 X1 (τ X0)
           grind)
        | exact resolve b0e21 b0e85
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e85
      have b0e185 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e179 X0 X1
           have i₂ := b0e50 X0
           grind)
        | exact superpose b0e50 b0e179
        | (have j0 := b0e179 X0 X1
           grind)
        | exact resolve b0e179 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179
      have b0e210 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 (σ X0)
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e14
        | (have j0 := b0e14 X1 (σ X0)
           grind)
        | exact resolve b0e14 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e246 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e12 (M.op (τ X0) (τ X0))
           have i₂ := b0e50 X0
           grind)
        | exact superpose b0e50 b0e12
        | exact resolve b0e12 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e262 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e89 (σ X0) (σ X1)
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e89
        | (have j0 := b0e89 (σ X0) (σ X1)
           grind)
        | exact resolve b0e89 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e286 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e22 X0 X1
           have i₂ := b0e89 X1 (τ X0)
           grind)
        | exact superpose b0e89 b0e22
        | (have j1 := b0e89 X1 (τ X0)
           grind)
        | exact resolve b0e22 b0e89
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e89
      have b0e309 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e286 X0 X1
           have i₂ := b0e50 X0
           grind)
        | exact superpose b0e50 b0e286
        | (have j0 := b0e286 X0 X1
           grind)
        | exact resolve b0e286 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e286
      have b0e318 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e262 X0 X1
           have i₂ := b0e48 X1
           grind)
        | exact superpose b0e48 b0e262
        | (have j0 := b0e262 X0 X1
           grind)
        | exact resolve b0e262 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e262
      have b0e325 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e309 X0 X1
           have i₂ := b0e246 X0
           grind)
        | exact superpose b0e246 b0e309
        | (have j0 := b0e309 X0 X1
           grind)
        | exact resolve b0e309 b0e246
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e309
      have b0e328 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e318 X0 X1
           have i₂ := b0e48 X1
           grind)
        | exact superpose b0e48 b0e318
        | (have j0 := b0e318 X0 X1
           grind)
        | exact resolve b0e318 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e318
      have b0e437 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 (τ X0)
           have i₂ := b0e246 X0
           grind)
        | exact superpose b0e246 b0e14
        | (have j0 := b0e14 X1 (τ X0)
           grind)
        | exact resolve b0e14 b0e246
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e246
      have b0e959 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
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
      have b0e974 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e93 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e975 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e93 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e93
      have b0e1017 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e959 X0 X1
           have j1 := b0e210 X1 (σ X0)
           grind)
        | (have r₁ := b0e959 X0 X0
           have r₂ := b0e210 X0 (σ X0)
           grind)
        | (have r₁ := b0e959 X0 X0
           have r₂ := b0e210 X0 (σ X0)
           grind)
        | exact resolve b0e959 b0e210
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e210 b0e959
      have b0e1070 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1017 X0 X1
           have i₂ := b0e48 X1
           grind)
        | exact superpose b0e48 b0e1017
        | (have j0 := b0e1017 X0 X1
           grind)
        | exact resolve b0e1017 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1017
      have b0e1105 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1070 X0 X1
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e1070
        | (have j0 := b0e1070 X0 X1
           grind)
        | exact resolve b0e1070 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1070
      have b0e1126 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1105 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e1105
        | (have j0 := b0e1105 X0 X1
           grind)
        | exact resolve b0e1105 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1105
      have b0e7792 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e437 X0 X1
           have i₂ := b0e325 X0 X1
           grind)
        | exact superpose b0e325 b0e437
        | (have j0 := b0e437 X0 X1
           have j1 := b0e325 X0 X1
           grind)
        | (have r₁ := b0e437 X0 X1
           have r₂ := b0e325 X0 X1
           grind)
        | exact resolve b0e437 b0e325
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e437
      have b0e7829 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e13 (M.op X0 X0)
           have i₂ := b0e325 X0 X1
           grind)
        | exact superpose b0e325 b0e13
        | (have j1 := b0e325 X0 X1
           grind)
        | exact resolve b0e13 b0e325
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e325
      have b0e7981 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have j0 := b0e7792 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7792
      have b0e8980 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e50 X1
           have i₂ := b0e185 X1 X0
           grind)
        | (have i₁ := b0e50 X0
           have i₂ := b0e185 X0 (τ X0)
           grind)
        | exact superpose b0e185 b0e50
        | (have j1 := b0e185 X1 X0
           grind)
        | exact resolve b0e50 b0e185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e185
      have b0e9881 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e75 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e75
        | exact resolve b0e75 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e9931 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e50 X0
           have i₂ := b0e75 X0 X1
           grind)
        | (have i₁ := b0e50 X0
           have i₂ := b0e75 X0 (τ X0)
           grind)
        | exact superpose b0e75 b0e50
        | (have j1 := b0e75 X0 X1
           grind)
        | exact resolve b0e50 b0e75
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75
      have b0e10285 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e9881 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e9881
        | (have j0 := b0e9881 X0 X1
           grind)
        | exact resolve b0e9881 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9881
      have b0e13170 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e1126 (τ X1) (τ X0)
           have i₂ := b0e112 X0 X1
           grind)
        | exact superpose b0e112 b0e1126
        | (have j0 := b0e1126 (τ X0) (τ X1)
           grind)
        | exact resolve b0e1126 b0e112
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1126
      have b0e13262 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e13170 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e13170
        | (have j0 := b0e13170 X0 X1
           grind)
        | exact resolve b0e13170 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13170
      have b0e13295 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e13262 X0 X1
           have i₂ := b0e50 X1
           grind)
        | exact superpose b0e50 b0e13262
        | (have j0 := b0e13262 X0 X1
           grind)
        | exact resolve b0e13262 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13262
      have b0e13324 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e13295 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e13295
        | (have j0 := b0e13295 X0 X1
           grind)
        | exact resolve b0e13295 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13295
      have b0e13341 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e13324 X0 X1
           have i₂ := b0e50 X0
           grind)
        | exact superpose b0e50 b0e13324
        | (have j0 := b0e13324 X0 X1
           grind)
        | exact resolve b0e13324 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13324
      have b0e13351 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e13341 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e13341
        | (have j0 := b0e13341 X0 X1
           grind)
        | exact resolve b0e13341 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13341
      have b0e13356 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e13351 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e13351
        | (have j0 := b0e13351 X0 X1
           grind)
        | exact resolve b0e13351 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13351
      have b0e13357 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e13356 X0 X1
           have i₂ := b0e50 X0
           grind)
        | exact superpose b0e50 b0e13356
        | (have j0 := b0e13356 X0 X1
           grind)
        | exact resolve b0e13356 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13356
      have b0e15393 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 (σ X0) (σ X1)
           have i₂ := b0e328 X0 X1
           grind)
        | exact superpose b0e328 b0e15
        | (have j0 := b0e15 (σ X0) (σ X1)
           have j1 := b0e328 X0 X1
           grind)
        | exact resolve b0e15 b0e328
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e328
      have b0e15549 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15393 X0 X1
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e15393
        | (have j0 := b0e15393 X0 X1
           grind)
        | exact resolve b0e15393 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15393
      have b0e15689 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15549 X0 X1
           have i₂ := b0e48 X1
           grind)
        | exact superpose b0e48 b0e15549
        | (have j0 := b0e15549 X0 X1
           grind)
        | exact resolve b0e15549 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15549
      have b0e15690 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e15689 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15689
      have b0e15780 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15690 X0 X1
           have i₂ := b0e48 X1
           grind)
        | exact superpose b0e48 b0e15690
        | (have j0 := b0e15690 X0 X1
           grind)
        | exact resolve b0e15690 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15690
      have b0e15814 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15780 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e15780
        | (have j0 := b0e15780 X0 X1
           grind)
        | exact resolve b0e15780 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15780
      have b0e15815 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e15814 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15814
      have b0e81687 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e21 X0 (τ X1)
           have i₂ := b0e7981 X1 (τ X0)
           grind)
        | exact superpose b0e7981 b0e21
        | (have j1 := b0e7981 X1 (τ X0)
           grind)
        | exact resolve b0e21 b0e7981
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21
      have b0e81739 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e26 (σ X1) X0
           have i₂ := b0e7981 (σ X0) X1
           grind)
        | exact superpose b0e7981 b0e26
        | (have j1 := b0e7981 (σ X0) X1
           grind)
        | exact resolve b0e26 b0e7981
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7981
      have b0e81749 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e81739 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e81739
        | (have j0 := b0e81739 X0 X1
           grind)
        | exact resolve b0e81739 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81739
      have b0e81763 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e81687 X0 X1
           have i₂ := b0e50 X0
           grind)
        | exact superpose b0e50 b0e81687
        | (have j0 := b0e81687 X0 X1
           grind)
        | exact resolve b0e81687 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50 b0e81687
      have b0e81791 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e81749 X0 X1
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e81749
        | (have j0 := b0e81749 X0 X1
           grind)
        | exact resolve b0e81749 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81749
      have b0e81796 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e81763 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e81763
        | (have j0 := b0e81763 X0 X1
           grind)
        | exact resolve b0e81763 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81763
      have b0e81813 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e81791 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e81791
        | (have j0 := b0e81791 X0 X1
           grind)
        | exact resolve b0e81791 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81791
      have b0e81818 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e81796 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e81796
        | (have j0 := b0e81796 X0 X1
           grind)
        | exact resolve b0e81796 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81796
      have b0e81828 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e81813 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e81813
        | (have j0 := b0e81813 X0 X1
           grind)
        | exact resolve b0e81813 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81813
      have b0e81831 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e81818 X0 X1
           have i₂ := b0e112 X1 X0
           grind)
        | exact superpose b0e112 b0e81818
        | (have j0 := b0e81818 X0 X1
           grind)
        | exact resolve b0e81818 b0e112
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e112 b0e81818
      have b0e81835 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e81828 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e81828
        | (have j0 := b0e81828 X0 X1
           grind)
        | exact resolve b0e81828 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81828
      have b0e82768 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e26 X1 X0
           have i₂ := b0e81835 (σ X0) X1
           grind)
        | exact superpose b0e81835 b0e26
        | (have j1 := b0e81835 (σ X0) X1
           grind)
        | exact resolve b0e26 b0e81835
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e82808 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e81835 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81835
      have b0e82869 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e82768 X0 X1
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e82768
        | (have j0 := b0e82768 X0 X1
           grind)
        | exact resolve b0e82768 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e82768
      have b0e83007 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e82869 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e82869
        | (have j0 := b0e82869 X0 X1
           grind)
        | exact resolve b0e82869 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e82869
      have b0e83444 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e82808 X0 X1
           have i₂ := b0e10285 X1 X0
           grind)
        | (have i₁ := b0e82808 X1 X1
           have i₂ := b0e10285 X0 X1
           grind)
        | exact superpose b0e10285 b0e82808
        | (have j0 := b0e82808 X0 X1
           have j1 := b0e10285 X1 X0
           grind)
        | (have r₁ := b0e82808 X1 X0
           have r₂ := b0e10285 X0 X1
           grind)
        | (have r₁ := b0e82808 X1 X1
           have r₂ := b0e10285 X1 X1
           grind)
        | exact resolve b0e82808 b0e10285
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10285 b0e82808
      have b0e83456 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e83444 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83444
      have b0e83486 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e83456 X0 X1
           have j1 := b0e14 X0 X1
           grind)
        | (have r₁ := b0e83456 X0 X1
           have r₂ := b0e14 X0 X1
           grind)
        | (have r₁ := b0e83456 X0 X0
           have r₂ := b0e14 X0 X0
           grind)
        | exact resolve b0e83456 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83456
      have b0e92032 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e13357 X0 X1
           have i₂ := b0e81831 X0 X1
           grind)
        | exact superpose b0e81831 b0e13357
        | (have j0 := b0e13357 X1 X0
           have j1 := b0e81831 X1 X0
           grind)
        | (have r₁ := b0e13357 X0 X1
           have r₂ := b0e81831 X0 X1
           grind)
        | (have r₁ := b0e13357 X1 X1
           have r₂ := b0e81831 X1 X1
           grind)
        | exact resolve b0e13357 b0e81831
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e92120 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e81831 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81831
      have b0e92134 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e92032 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e92032
      have b0e92212 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e92134 X0 X1
           have j1 := b0e92120 X1 X0
           grind)
        | (have r₁ := b0e92134 X0 X1
           have r₂ := b0e92120 X0 X1
           grind)
        | (have r₁ := b0e92134 X1 X0
           have r₂ := b0e92120 X0 X1
           grind)
        | (have r₁ := b0e92134 X1 X1
           have r₂ := b0e92120 X1 X1
           grind)
        | exact resolve b0e92134 b0e92120
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e92120 b0e92134
      have b0e107279 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e92212 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e92212
        | (have j0 := b0e92212 (σ X0) X1
           grind)
        | exact resolve b0e92212 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e92212
      have b0e107344 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e107279 X0 X1
           have i₂ := b0e26 X1 X0
           grind)
        | exact superpose b0e26 b0e107279
        | (have j0 := b0e107279 X0 X1
           grind)
        | exact resolve b0e107279 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26 b0e107279
      have b0e145094 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e32 X0 (σ X1)
           have i₂ := b0e83007 X1 (σ X0)
           grind)
        | exact superpose b0e83007 b0e32
        | (have j1 := b0e83007 X1 (σ X0)
           grind)
        | exact resolve b0e32 b0e83007
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83007
      have b0e145154 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e145094 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e145094
        | (have j0 := b0e145094 X0 X1
           grind)
        | exact resolve b0e145094 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e145094
      have b0e145182 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e145154 X0 X1
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e145154
        | (have j0 := b0e145154 X0 X1
           grind)
        | exact resolve b0e145154 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e145154
      have b0e145199 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e145182 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e145182
        | (have j0 := b0e145182 X0 X1
           grind)
        | exact resolve b0e145182 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e145182
      have b0e145212 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e145199 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e145199
        | (have j0 := b0e145199 X0 X1
           grind)
        | exact resolve b0e145199 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e145199
      have b0e145217 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e145212 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e145212
        | (have j0 := b0e145212 X0 X1
           grind)
        | exact resolve b0e145212 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e145212
      have b0e154394 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e145217 y x
           grind)
        | exact superpose b0e145217 b0e18
        | (have j1 := b0e145217 y x
           grind)
        | exact resolve b0e18 b0e145217
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e145217
      have b0e154533 : (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
        first
        | (have j1 := b0e83486 y x
           grind)
        | (have r₁ := b0e154394
           have r₂ := b0e83486 y x
           grind)
        | exact resolve b0e154394 b0e83486
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83486 b0e154394
      have b0e157658 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e154533
           have i₂ := b0e16 y x
           grind)
        | exact superpose b0e16 b0e154533
        | (have j1 := b0e16 y x
           grind)
        | exact resolve b0e154533 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e157676 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e13357 y x
           have i₂ := b0e154533
           grind)
        | exact superpose b0e154533 b0e13357
        | (have j0 := b0e13357 y x
           grind)
        | (have r₁ := b0e13357 y x
           have r₂ := b0e154533
           grind)
        | exact resolve b0e13357 b0e154533
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13357
      have b0e157691 : (M.op y y) ≠ (M.op x x) ∨ (M.op y y) = (k y x) := by grind
      have b0e157695 : (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by grind
      clear b0e157676
      have b0e157704 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e157658
      have b0e157711 : (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have r₁ := b0e157695
           have r₂ := b0e157691
           grind)
        | exact resolve b0e157695 b0e157691
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e157695
      have b0e207506 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e32 X0 (σ X1)
           have i₂ := b0e107344 X1 (σ X0)
           grind)
        | exact superpose b0e107344 b0e32
        | (have j1 := b0e107344 X1 (σ X0)
           grind)
        | exact resolve b0e32 b0e107344
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e107344
      have b0e207511 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e207506 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e207506
        | (have j0 := b0e207506 X0 X1
           grind)
        | exact resolve b0e207506 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e207506
      have b0e207530 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e207511 X0 X1
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e207511
        | (have j0 := b0e207511 X0 X1
           grind)
        | exact resolve b0e207511 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e207511
      have b0e207541 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e207530 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e207530
        | (have j0 := b0e207530 X0 X1
           grind)
        | exact resolve b0e207530 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e207530
      have b0e207547 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e207541 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e207541
        | (have j0 := b0e207541 X0 X1
           grind)
        | exact resolve b0e207541 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e207541
      have b0e207548 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e207547 X0 X1
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e207547
        | (have j0 := b0e207547 X0 X1
           grind)
        | exact resolve b0e207547 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e207547
      have b0e208392 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e207548 y x
           grind)
        | exact superpose b0e207548 b0e18
        | (have j1 := b0e207548 y x
           grind)
        | exact resolve b0e18 b0e207548
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e207548
      have b0e318828 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (k X1 X0) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e7829 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e7829
        | (have j0 := b0e7829 (σ X0) X1
           grind)
        | exact resolve b0e7829 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7829
      have b0e318848 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (k X1 X0) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e318828 X0 X1
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e318828
        | (have j0 := b0e318828 X0 X1
           grind)
        | exact resolve b0e318828 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e318828
      have b0e318851 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e318848 X0 X1
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e318848
        | (have j0 := b0e318848 X0 X1
           grind)
        | exact resolve b0e318848 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e318848
      have b0e318854 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e318851 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e318851
        | (have j0 := b0e318851 X0 X1
           grind)
        | exact resolve b0e318851 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e318851
      have b0e326311 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e318854 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e318854
      have b0e335361 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e326311 x y
           have i₂ := b0e157711
           grind)
        | exact superpose b0e157711 b0e326311
        | (have j0 := b0e326311 x y
           grind)
        | exact resolve b0e326311 b0e157711
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e326311
      have b0e335365 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e335361
      have b0e345725 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e8980 X0 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e8980
        | (have j0 := b0e8980 X1 (σ X0)
           grind)
        | exact resolve b0e8980 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8980
      have b0e345745 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e345725 X0 X1
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e345725
        | (have j0 := b0e345725 X0 X1
           grind)
        | exact resolve b0e345725 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e345725
      have b0e345748 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e345745 X0 X1
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e345745
        | (have j0 := b0e345745 X0 X1
           grind)
        | exact resolve b0e345745 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e345745
      have b0e345751 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e345748 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e345748
        | (have j0 := b0e345748 X0 X1
           grind)
        | exact resolve b0e345748 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e345748
      have b0e346468 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e345751 y x
           have i₂ := b0e154533
           grind)
        | exact superpose b0e154533 b0e345751
        | (have j0 := b0e345751 y x
           grind)
        | exact resolve b0e345751 b0e154533
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e154533 b0e345751
      have b0e346559 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op y y) = (k y x) := by
        first
        | (have j1 := b0e14 y x
           grind)
        | (have r₁ := b0e346468
           have r₂ := b0e14 y x
           grind)
        | exact resolve b0e346468 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e346468
      have b0e353648 : (M.op x x) = (τ (σ (M.op y y))) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e12 (M.op x x)
           have i₂ := b0e346559
           grind)
        | exact superpose b0e346559 b0e12
        | exact resolve b0e12 b0e346559
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e346559
      have b0e353684 : (M.op y y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e353648
           have i₂ := b0e12 (M.op y y)
           grind)
        | exact superpose b0e12 b0e353648
        | exact resolve b0e353648 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e353648
      have b0e353685 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op y y) = (k y x) := by
        first
        | (have r₁ := b0e353684
           have r₂ := b0e157691
           grind)
        | exact resolve b0e353684 b0e157691
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e157691 b0e353684
      have b0e354408 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e208392
           have i₂ := b0e353685
           grind)
        | exact superpose b0e353685 b0e208392
        | (have r₁ := b0e208392
           have r₂ := b0e353685
           grind)
        | exact resolve b0e208392 b0e353685
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e208392 b0e353685
      have b0e354436 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by grind
      clear b0e354408
      have b0e354437 : (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by grind
      clear b0e354436
      have b0e360881 : (M.op x y) ≠ (M.op y y) ∨ (M.op y y) = (k y x) := by grind
      clear b0e354437
      have b0e360889 : (M.op y y) = (k y x) := by
        first
        | (have r₁ := b0e360881
           have r₂ := b0e157711
           grind)
        | exact resolve b0e360881 b0e157711
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e157711 b0e360881
      have b0e368752 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e974 x y
           have i₂ := b0e360889
           grind)
        | exact superpose b0e360889 b0e974
        | (have j0 := b0e974 x y
           grind)
        | exact resolve b0e974 b0e360889
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e974
      have b0e368753 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e975 x y
           have i₂ := b0e360889
           grind)
        | exact superpose b0e360889 b0e975
        | (have j0 := b0e975 x y
           grind)
        | exact resolve b0e975 b0e360889
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e975
      have b0e368780 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
      clear b0e368753
      have b0e368781 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
      clear b0e368752
      have b0e396861 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e368780
           grind)
        | exact superpose b0e368780 b0e18
        | exact resolve b0e18 b0e368780
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e368780
      have b0e397646 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e396861
           have i₂ := b0e157704
           grind)
        | exact superpose b0e157704 b0e396861
        | exact resolve b0e396861 b0e157704
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e157704 b0e396861
      have b0e397651 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e397646
      have b0e404372 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e397651
           grind)
        | exact superpose b0e397651 b0e18
        | exact resolve b0e18 b0e397651
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2606365 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e9931 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e9931
        | exact resolve b0e9931 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9931
      have b0e2606371 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e2606365 X0 X1
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e2606365
        | (have j0 := b0e2606365 X0 X1
           grind)
        | exact resolve b0e2606365 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e2606365
      have b0e2606374 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e2606371 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e2606371
        | (have j0 := b0e2606371 X0 X1
           grind)
        | exact resolve b0e2606371 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2606371
      have b0e2606380 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e2606374 x y
           have i₂ := b0e360889
           grind)
        | exact superpose b0e360889 b0e2606374
        | (have j0 := b0e2606374 x y
           grind)
        | exact resolve b0e2606374 b0e360889
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2606374
      have b0e2606391 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have r₁ := b0e2606380
           have r₂ := b0e335365
           grind)
        | exact resolve b0e2606380 b0e335365
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e335365 b0e2606380
      have b0e2606763 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e15815 y x
           have i₂ := b0e360889
           grind)
        | exact superpose b0e360889 b0e15815
        | (have j0 := b0e15815 y x
           grind)
        | exact resolve b0e15815 b0e360889
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15815
      have b0e2606764 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
      clear b0e2606763
      have b0e2606768 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e397651
           have i₂ := b0e2606764
           grind)
        | exact superpose b0e2606764 b0e397651
        | exact resolve b0e397651 b0e2606764
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e397651 b0e2606764
      have b0e2606770 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e2606768
      have b0e2606782 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e2606391
           have i₂ := b0e2606770
           grind)
        | exact superpose b0e2606770 b0e2606391
        | exact resolve b0e2606391 b0e2606770
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2606391 b0e2606770
      have b0e2606809 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e2606782
      have b0e2606831 : (M.op x y) = (M.op y y) := by
        first
        | (have r₁ := b0e2606809
           have r₂ := b0e404372
           grind)
        | exact resolve b0e2606809 b0e404372
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e404372 b0e2606809
      have b0e2606849 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e2606831
           grind)
        | exact superpose b0e2606831 b0e15
        | (have j0 := b0e15 y y
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e2606831
           grind)
        | exact resolve b0e15 b0e2606831
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2606879 : (M.op y y) = (M.op x x) ∨ (M.op x x) = (k y x) := by grind
      clear b0e2606849
      have b0e2606882 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
        first
        | (have i₁ := b0e2606879
           have i₂ := b0e360889
           grind)
        | exact superpose b0e360889 b0e2606879
        | exact resolve b0e2606879 b0e360889
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e360889 b0e2606879
      have b0e2606883 : (M.op y y) = (M.op x x) := by grind
      clear b0e2606882
      have b0e2606901 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e368781
           have i₂ := b0e2606883
           grind)
        | exact superpose b0e2606883 b0e368781
        | exact resolve b0e368781 b0e2606883
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e368781 b0e2606883
      have b0e2607171 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
      clear b0e2606901
      have b0e2607220 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e2607171
           grind)
        | exact superpose b0e2607171 b0e18
        | exact resolve b0e18 b0e2607171
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2607171
      have b0e2607250 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e2607220
           have i₂ := b0e2606831
           grind)
        | exact superpose b0e2606831 b0e2607220
        | exact resolve b0e2607220 b0e2606831
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2606831 b0e2607220
      have b0e2607251 : False := by grind
      exact b0e2607251
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : (M.op y x) = (M.op y y) := by grind
        have b1e21 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e46 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
          first
          | (have i₁ := b1e15 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 y y
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e47 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : (M.op (σ y) (σ x)) = (k (σ x) (σ x)) := by grind
        clear b1e47
        have b1e51 : (M.op x x) = (k x y) := by grind
        clear b1e46
        have b1e52 : (M.op (σ y) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e50
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e50
          | exact resolve b1e50 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e53 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e49 x
             grind)
          | exact superpose b1e49 b1e52
          | exact resolve b1e52 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e49 (σ X0)
             grind)
          | exact superpose b1e49 b1e18
          | exact resolve b1e18 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e62 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e55 X0
             have i₂ := b1e49 X0
             grind)
          | exact superpose b1e49 b1e55
          | exact resolve b1e55 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49 b1e55
        have b1e68 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e16 (σ x) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) X0
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e71 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e68 X0
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e68
          | (have j0 := b1e68 X0
             grind)
          | exact resolve b1e68 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e123 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e21
          | exact resolve b1e21 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e126 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e123
             have i₂ := b1e62 y
             grind)
          | exact superpose b1e62 b1e123
          | exact resolve b1e123 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e123
        have b1e556 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e71 (σ y)
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e71
          | (have j0 := b1e71 (σ y)
             grind)
          | (have r₁ := b1e71 (σ y)
             have r₂ := b1e53
             grind)
          | exact resolve b1e71 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53 b1e71
        have b1e557 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e556
        have b1e558 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e557
             have i₂ := b1e62 y
             grind)
          | exact superpose b1e62 b1e557
          | exact resolve b1e557 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e557
        have b1e562 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e558
             have r₂ := b1e126
             grind)
          | exact resolve b1e558 b1e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e558
        have b1e565 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e562
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e562
          | exact resolve b1e562 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e562
        have b1e567 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e565
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e565
          | exact resolve b1e565 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e565
        have b1e569 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e567
             have i₂ := b1e62 y
             grind)
          | exact superpose b1e62 b1e567
          | exact resolve b1e567 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62 b1e567
        have b1e570 : False := by grind
        exact b1e570
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op y x) = (M.op y y) := by grind
        have b2e21 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e45 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
          first
          | (have i₁ := b2e15 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 y y
             grind)
          | (have r₁ := b2e15 x y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e47 : (M.op x x) = (k x y) := by grind
        clear b2e45
        have b2e49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e46 (σ X0)
             grind)
          | exact superpose b2e46 b2e18
          | exact resolve b2e18 b2e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e49 X0
             have i₂ := b2e46 X0
             grind)
          | exact superpose b2e46 b2e49
          | exact resolve b2e49 b2e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46 b2e49
        have b2e83 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) (σ x)
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
        have b2e137 : (M.op (σ y) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e56 x
             grind)
          | exact superpose b2e56 b2e22
          | exact resolve b2e22 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e692 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e83 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e83
        have b2e693 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e692
             have r₂ := b2e21
             grind)
          | exact resolve b2e692 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e692
        have b2e695 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e693
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e693
          | exact resolve b2e693 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e693
        have b2e697 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e695
             have i₂ := b2e47
             grind)
          | exact superpose b2e47 b2e695
          | exact resolve b2e695 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47 b2e695
        have b2e698 : False := by grind
        exact b2e698
  · rcases eq_or_ne (M.op x x) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op y x) ≠ (M.op y y) := by grind
        have b3e21 : (M.op y x) = (M.op x x) := by grind
        have b3e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e47 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ y) (σ y)
             grind)
          | (have r₁ := b3e15 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e50 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e47
        have b3e52 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e50
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e50
          | exact resolve b3e50 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e68 : ∀ X0 : G, (M.op y x) ≠ (M.op X0 x) ∨ (M.op X0 X0) = (M.op X0 x) ∨ (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e16 x X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 x X0
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e74 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e52
             grind)
          | exact superpose b3e52 b3e15
          | exact resolve b3e15 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e75 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b3e74
        have b3e76 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e75
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e75
          | exact resolve b3e75 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e77 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e76
             have i₂ := b3e49 x
             grind)
          | exact superpose b3e49 b3e76
          | exact resolve b3e76 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49 b3e76
        have b3e78 : (σ (k x y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e77
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e77
          | exact resolve b3e77 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e77
        have b3e129 : (k x y) = (τ (σ (M.op y x))) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e78
             grind)
          | exact superpose b3e78 b3e13
          | exact resolve b3e13 b3e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78
        have b3e130 : (M.op y x) = (k x y) := by
          first
          | (have i₁ := b3e129
             have i₂ := b3e13 (M.op y x)
             grind)
          | exact superpose b3e13 b3e129
          | exact resolve b3e129 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e129
        have b3e167 : (M.op y x) = (M.op y y) ∨ (M.op y y) = (k x y) := by
          first
          | (have j0 := b3e68 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e168 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b3e167
             have r₂ := b3e20
             grind)
          | exact resolve b3e167 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e167
        have b3e173 : (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b3e130
             have i₂ := b3e168
             grind)
          | exact superpose b3e168 b3e130
          | exact resolve b3e130 b3e168
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e130 b3e168
        have b3e178 : False := by grind
        exact b3e178
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b4e22 : (M.op y x) = (M.op x x) := by grind
          have b4e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e23
            | exact resolve b4e23 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (M.op y y) ≠ (M.op x x) := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e21
            | exact resolve b4e21 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e27 X0 X1
               grind)
            | exact superpose b4e27 b4e14
            | exact resolve b4e14 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e28 X1 X0
               grind)
            | exact superpose b4e28 b4e14
            | exact resolve b4e14 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e32
            | exact resolve b4e32 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e61 (σ X0)
               grind)
            | exact superpose b4e61 b4e19
            | exact resolve b4e19 b4e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e66 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b4e28 X0 (τ X0)
               have i₂ := b4e61 (τ X0)
               grind)
            | exact superpose b4e61 b4e28
            | exact resolve b4e28 b4e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e69 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e66 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e66
            | exact resolve b4e66 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66
          have b4e72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e63 X0
               have i₂ := b4e61 X0
               grind)
            | exact superpose b4e61 b4e63
            | exact resolve b4e63 b4e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e63
          have b4e75 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e69 X0
               have i₂ := b4e61 X0
               grind)
            | exact superpose b4e61 b4e69
            | exact resolve b4e69 b4e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e61 b4e69
          have b4e96 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e16 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X0 X0
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e110 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e114 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e28 X0 X1
               have i₂ := b4e18 X1 (τ X0)
               grind)
            | exact superpose b4e18 b4e28
            | (have j1 := b4e18 X1 (τ X0)
               grind)
            | exact resolve b4e28 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e115 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
          have b4e119 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e120 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e122 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e110 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e110
          have b4e125 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e96 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96
          have b4e128 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e115 X0 X1
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e115
            | (have j0 := b4e115 X0 X1
               grind)
            | exact resolve b4e115 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115
          have b4e131 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e122 X0 X1
               have j1 := b4e120 X1 X0
               grind)
            | (have r₁ := b4e122 X0 X1
               have r₂ := b4e120 X0 X1
               grind)
            | (have r₁ := b4e122 X1 X0
               have r₂ := b4e120 X0 X1
               grind)
            | (have r₁ := b4e122 X1 X1
               have r₂ := b4e120 X1 X1
               grind)
            | exact resolve b4e122 b4e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e120 b4e122
          have b4e137 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e128 X0 X1
               have i₂ := b4e72 X1
               grind)
            | exact superpose b4e72 b4e128
            | (have j0 := b4e128 X0 X1
               grind)
            | exact resolve b4e128 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e128
          have b4e144 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e72 y
               grind)
            | exact superpose b4e72 b4e25
            | exact resolve b4e25 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e148 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 (σ X0)
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e16
            | (have j0 := b4e16 X1 (σ X0)
               grind)
            | exact resolve b4e16 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e153 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e144
               have i₂ := b4e72 x
               grind)
            | exact superpose b4e72 b4e144
            | exact resolve b4e144 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e144
          have b4e178 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e14 (M.op (τ X0) (τ X0))
               have i₂ := b4e75 X0
               grind)
            | exact superpose b4e75 b4e14
            | exact resolve b4e14 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e217 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e27 X0 X1
               have i₂ := b4e125 X1 (τ X0)
               grind)
            | exact superpose b4e125 b4e27
            | (have j1 := b4e125 X1 (τ X0)
               grind)
            | exact resolve b4e27 b4e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e223 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e217 X0 X1
               have i₂ := b4e75 X0
               grind)
            | exact superpose b4e75 b4e217
            | (have j0 := b4e217 X0 X1
               grind)
            | exact resolve b4e217 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e217
          have b4e236 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e223 X0 X1
               have i₂ := b4e178 X0
               grind)
            | exact superpose b4e178 b4e223
            | (have j0 := b4e223 X0 X1
               grind)
            | exact resolve b4e223 b4e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e223
          have b4e301 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 (τ X0)
               have i₂ := b4e178 X0
               grind)
            | exact superpose b4e178 b4e16
            | (have j0 := b4e16 X1 (τ X0)
               grind)
            | exact resolve b4e16 b4e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e351 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e28 X0 X1
               have i₂ := b4e131 X1 (τ X0)
               grind)
            | exact superpose b4e131 b4e28
            | (have j1 := b4e131 X1 (τ X0)
               grind)
            | exact resolve b4e28 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e131
          have b4e377 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e351 X0 X1
               have i₂ := b4e75 X0
               grind)
            | exact superpose b4e75 b4e351
            | (have j0 := b4e351 X0 X1
               grind)
            | exact resolve b4e351 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e351
          have b4e398 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e377 X0 X1
               have i₂ := b4e178 X0
               grind)
            | exact superpose b4e178 b4e377
            | (have j0 := b4e377 X0 X1
               grind)
            | exact resolve b4e377 b4e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e178 b4e377
          have b4e1229 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (σ X0) (σ X1)
               have i₂ := b4e137 X1 X0
               grind)
            | exact superpose b4e137 b4e16
            | (have j0 := b4e16 (σ X0) (σ X1)
               have j1 := b4e137 X1 X0
               grind)
            | exact resolve b4e16 b4e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137
          have b4e1287 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e1229 X0 X1
               have j1 := b4e148 X1 (σ X0)
               grind)
            | (have r₁ := b4e1229 X0 X0
               have r₂ := b4e148 X0 (σ X0)
               grind)
            | (have r₁ := b4e1229 X0 X0
               have r₂ := b4e148 X0 (σ X0)
               grind)
            | exact resolve b4e1229 b4e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e148 b4e1229
          have b4e1340 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1287 X0 X1
               have i₂ := b4e72 X1
               grind)
            | exact superpose b4e72 b4e1287
            | (have j0 := b4e1287 X0 X1
               grind)
            | exact resolve b4e1287 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1287
          have b4e1375 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1340 X0 X1
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e1340
            | (have j0 := b4e1340 X0 X1
               grind)
            | exact resolve b4e1340 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1340
          have b4e1396 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1375 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e1375
            | (have j0 := b4e1375 X0 X1
               grind)
            | exact resolve b4e1375 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1375
          have b4e6317 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (k (τ X1) X0) = (M.op X0 (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e15 (M.op X1 X1)
               have i₂ := b4e236 X1 X0
               grind)
            | exact superpose b4e236 b4e15
            | (have j1 := b4e236 X1 X0
               grind)
            | exact resolve b4e15 b4e236
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e236
          have b4e8217 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e301 X0 X1
               have i₂ := b4e398 X0 X1
               grind)
            | exact superpose b4e398 b4e301
            | (have j0 := b4e301 X0 X1
               have j1 := b4e398 X0 X1
               grind)
            | (have r₁ := b4e301 X0 X1
               have r₂ := b4e398 X0 X1
               grind)
            | exact resolve b4e301 b4e398
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e301
          have b4e8256 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e15 (M.op X0 X0)
               have i₂ := b4e398 X0 X1
               grind)
            | exact superpose b4e398 b4e15
            | (have j1 := b4e398 X0 X1
               grind)
            | exact resolve b4e15 b4e398
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e398
          have b4e8414 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b4e8217 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8217
          have b4e9443 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e114 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e114
            | exact resolve b4e114 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e114
          have b4e9827 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e9443 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e9443
            | (have j0 := b4e9443 X0 X1
               grind)
            | exact resolve b4e9443 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9443
          have b4e13684 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e1396 (τ X1) (τ X0)
               have i₂ := b4e41 X0 X1
               grind)
            | exact superpose b4e41 b4e1396
            | (have j0 := b4e1396 (τ X0) (τ X1)
               grind)
            | exact resolve b4e1396 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1396
          have b4e13782 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13684 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e13684
            | (have j0 := b4e13684 X0 X1
               grind)
            | exact resolve b4e13684 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13684
          have b4e13815 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13782 X0 X1
               have i₂ := b4e75 X1
               grind)
            | exact superpose b4e75 b4e13782
            | (have j0 := b4e13782 X0 X1
               grind)
            | exact resolve b4e13782 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13782
          have b4e13844 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13815 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e13815
            | (have j0 := b4e13815 X0 X1
               grind)
            | exact resolve b4e13815 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13815
          have b4e13863 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13844 X0 X1
               have i₂ := b4e75 X0
               grind)
            | exact superpose b4e75 b4e13844
            | (have j0 := b4e13844 X0 X1
               grind)
            | exact resolve b4e13844 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13844
          have b4e13876 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13863 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e13863
            | (have j0 := b4e13863 X0 X1
               grind)
            | exact resolve b4e13863 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13863
          have b4e13884 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13876 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e13876
            | (have j0 := b4e13876 X0 X1
               grind)
            | exact resolve b4e13876 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13876
          have b4e13888 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13884 X0 X1
               have i₂ := b4e75 X0
               grind)
            | exact superpose b4e75 b4e13884
            | (have j0 := b4e13884 X0 X1
               grind)
            | exact resolve b4e13884 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13884
          have b4e83771 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e27 X0 (τ X1)
               have i₂ := b4e8414 X1 (τ X0)
               grind)
            | exact superpose b4e8414 b4e27
            | (have j1 := b4e8414 X1 (τ X0)
               grind)
            | exact resolve b4e27 b4e8414
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e83822 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 (σ X1) X0
               have i₂ := b4e8414 (σ X0) X1
               grind)
            | exact superpose b4e8414 b4e32
            | (have j1 := b4e8414 (σ X0) X1
               grind)
            | exact resolve b4e32 b4e8414
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8414
          have b4e83832 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e83822 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e83822
            | (have j0 := b4e83822 X0 X1
               grind)
            | exact resolve b4e83822 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83822
          have b4e83846 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e83771 X0 X1
               have i₂ := b4e75 X0
               grind)
            | exact superpose b4e75 b4e83771
            | (have j0 := b4e83771 X0 X1
               grind)
            | exact resolve b4e83771 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75 b4e83771
          have b4e83873 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e83832 X0 X1
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e83832
            | (have j0 := b4e83832 X0 X1
               grind)
            | exact resolve b4e83832 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83832
          have b4e83878 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e83846 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e83846
            | (have j0 := b4e83846 X0 X1
               grind)
            | exact resolve b4e83846 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83846
          have b4e83895 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e83873 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e83873
            | (have j0 := b4e83873 X0 X1
               grind)
            | exact resolve b4e83873 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83873
          have b4e83900 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e83878 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e83878
            | (have j0 := b4e83878 X0 X1
               grind)
            | exact resolve b4e83878 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83878
          have b4e83910 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e83895 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e83895
            | (have j0 := b4e83895 X0 X1
               grind)
            | exact resolve b4e83895 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83895
          have b4e83913 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e83900 X0 X1
               have i₂ := b4e41 X1 X0
               grind)
            | exact superpose b4e41 b4e83900
            | (have j0 := b4e83900 X0 X1
               grind)
            | exact resolve b4e83900 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e83900
          have b4e83917 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e83910 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e83910
            | (have j0 := b4e83910 X0 X1
               grind)
            | exact resolve b4e83910 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83910
          have b4e84819 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X1 X0
               have i₂ := b4e83917 (σ X0) X1
               grind)
            | exact superpose b4e83917 b4e32
            | (have j1 := b4e83917 (σ X0) X1
               grind)
            | exact resolve b4e32 b4e83917
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e84859 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e83917 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83917
          have b4e84920 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e84819 X0 X1
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e84819
            | (have j0 := b4e84819 X0 X1
               grind)
            | exact resolve b4e84819 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84819
          have b4e85058 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e84920 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e84920
            | (have j0 := b4e84920 X0 X1
               grind)
            | exact resolve b4e84920 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84920
          have b4e85481 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e84859 X0 X1
               have i₂ := b4e9827 X1 X0
               grind)
            | (have i₁ := b4e84859 X1 X1
               have i₂ := b4e9827 X0 X1
               grind)
            | exact superpose b4e9827 b4e84859
            | (have j0 := b4e84859 X0 X1
               have j1 := b4e9827 X1 X0
               grind)
            | (have r₁ := b4e84859 X1 X0
               have r₂ := b4e9827 X0 X1
               grind)
            | (have r₁ := b4e84859 X1 X1
               have r₂ := b4e9827 X1 X1
               grind)
            | exact resolve b4e84859 b4e9827
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9827 b4e84859
          have b4e85495 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e85481 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85481
          have b4e85526 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e85495 X0 X1
               have j1 := b4e16 X0 X1
               grind)
            | (have r₁ := b4e85495 X0 X1
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e85495 X0 X0
               have r₂ := b4e16 X0 X0
               grind)
            | exact resolve b4e85495 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85495
          have b4e93932 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e83913 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e83913
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e83913 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e94011 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13888 X0 X1
               have i₂ := b4e83913 X0 X1
               grind)
            | exact superpose b4e83913 b4e13888
            | (have j0 := b4e13888 X1 X0
               have j1 := b4e83913 X1 X0
               grind)
            | (have r₁ := b4e13888 X0 X1
               have r₂ := b4e83913 X0 X1
               grind)
            | (have r₁ := b4e13888 X1 X1
               have r₂ := b4e83913 X1 X1
               grind)
            | exact resolve b4e13888 b4e83913
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e94098 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e83913 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83913
          have b4e94112 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e94011 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94011
          have b4e94141 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e93932 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93932
          have b4e94190 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e94112 X0 X1
               have j1 := b4e94098 X1 X0
               grind)
            | (have r₁ := b4e94112 X0 X1
               have r₂ := b4e94098 X0 X1
               grind)
            | (have r₁ := b4e94112 X1 X0
               have r₂ := b4e94098 X0 X1
               grind)
            | (have r₁ := b4e94112 X1 X1
               have r₂ := b4e94098 X1 X1
               grind)
            | exact resolve b4e94112 b4e94098
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94098 b4e94112
          have b4e96159 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X1 X1
               have i₂ := b4e94141 X0 X1
               grind)
            | (have i₁ := b4e17 X1 X0
               have i₂ := b4e94141 X0 X1
               grind)
            | exact superpose b4e94141 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e94141 X1 X0
               grind)
            | (have r₁ := b4e17 X1 X0
               have r₂ := b4e94141 X0 X1
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e94141 X1 X1
               grind)
            | exact resolve b4e17 b4e94141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e96222 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e94141 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94141
          have b4e96233 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e96159 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96159
          have b4e96255 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e96233 X0 X1
               have j1 := b4e96222 X1 X0
               grind)
            | (have r₁ := b4e96233 X0 X1
               have r₂ := b4e96222 X0 X1
               grind)
            | (have r₁ := b4e96233 X1 X0
               have r₂ := b4e96222 X0 X1
               grind)
            | (have r₁ := b4e96233 X1 X1
               have r₂ := b4e96222 X1 X1
               grind)
            | exact resolve b4e96233 b4e96222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96222 b4e96233
          have b4e108935 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e94190 (σ X1) (σ X0)
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e94190
            | (have j0 := b4e94190 (σ X1) (σ X0)
               grind)
            | exact resolve b4e94190 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94190
          have b4e108987 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e108935 X0 X1
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e108935
            | (have j0 := b4e108935 X0 X1
               grind)
            | exact resolve b4e108935 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e108935
          have b4e109008 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) X0) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e108987 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e108987
            | (have j0 := b4e108987 X0 X1
               grind)
            | exact resolve b4e108987 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e108987
          have b4e109016 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e109008 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e109008
            | (have j0 := b4e109008 X0 X1
               grind)
            | exact resolve b4e109008 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109008
          have b4e109020 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e109016 X0 X1
               have i₂ := b4e14 (k X0 X1)
               grind)
            | exact superpose b4e14 b4e109016
            | (have j0 := b4e109016 X0 X1
               grind)
            | exact resolve b4e109016 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109016
          have b4e109023 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e109020 X0 X1
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e109020
            | (have j0 := b4e109020 X0 X1
               grind)
            | exact resolve b4e109020 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109020
          have b4e113242 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (τ (M.op (σ X0) X1)) = (M.op (τ (σ X0)) (τ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X1 X0
               have i₂ := b4e96255 X1 (σ X0)
               grind)
            | exact superpose b4e96255 b4e32
            | (have j1 := b4e96255 X1 (σ X0)
               grind)
            | exact resolve b4e32 b4e96255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32 b4e96255
          have b4e113266 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (τ (M.op (σ X0) X1)) = (M.op (τ (σ X0)) (τ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e113242 X0 X1
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e113242
            | (have j0 := b4e113242 X0 X1
               grind)
            | exact resolve b4e113242 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e113242
          have b4e113280 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ X1) X0) ∨ (τ (M.op (σ X0) X1)) = (M.op (τ (σ X0)) (τ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e113266 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e113266
            | (have j0 := b4e113266 X0 X1
               grind)
            | exact resolve b4e113266 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e113266
          have b4e113289 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e113280 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e113280
            | (have j0 := b4e113280 X0 X1
               grind)
            | exact resolve b4e113280 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e113280
          have b4e113293 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (τ (M.op (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = (k (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e113289 X0 X1
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e113289
            | (have j0 := b4e113289 X0 X1
               grind)
            | exact resolve b4e113289 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e113289
          have b4e137592 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e38 X0 (σ X1)
               have i₂ := b4e85058 X1 (σ X0)
               grind)
            | exact superpose b4e85058 b4e38
            | (have j1 := b4e85058 X1 (σ X0)
               grind)
            | exact resolve b4e38 b4e85058
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38 b4e85058
          have b4e137652 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e137592 X0 X1
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e137592
            | (have j0 := b4e137592 X0 X1
               grind)
            | exact resolve b4e137592 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137592
          have b4e137680 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e137652 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e137652
            | (have j0 := b4e137652 X0 X1
               grind)
            | exact resolve b4e137652 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137652
          have b4e137697 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e137680 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e137680
            | (have j0 := b4e137680 X0 X1
               grind)
            | exact resolve b4e137680 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137680
          have b4e137710 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e137697 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e137697
            | (have j0 := b4e137697 X0 X1
               grind)
            | exact resolve b4e137697 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137697
          have b4e137715 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e137710 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e137710
            | (have j0 := b4e137710 X0 X1
               grind)
            | exact resolve b4e137710 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137710
          have b4e144330 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e137715 y x
               grind)
            | exact superpose b4e137715 b4e20
            | (have j1 := b4e137715 y x
               grind)
            | exact resolve b4e20 b4e137715
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137715
          have b4e144466 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j1 := b4e85526 y x
               grind)
            | (have r₁ := b4e144330
               have r₂ := b4e85526 y x
               grind)
            | exact resolve b4e144330 b4e85526
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85526 b4e144330
          have b4e144537 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e144466
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e144466
            | (have j1 := b4e18 y x
               grind)
            | exact resolve b4e144466 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e144466
          have b4e144579 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b4e144537
          have b4e343147 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e6317 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e6317
            | (have j0 := b4e6317 X1 (σ X0)
               grind)
            | exact resolve b4e6317 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6317
          have b4e343169 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e343147 X0 X1
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e343147
            | (have j0 := b4e343147 X0 X1
               grind)
            | exact resolve b4e343147 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e343147
          have b4e343172 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e343169 X0 X1
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e343169
            | (have j0 := b4e343169 X0 X1
               grind)
            | exact resolve b4e343169 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e343169
          have b4e343175 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e343172 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e343172
            | (have j0 := b4e343172 X0 X1
               grind)
            | exact resolve b4e343172 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e343172
          have b4e350940 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e8256 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e8256
            | (have j0 := b4e8256 (σ X0) X1
               grind)
            | exact resolve b4e8256 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8256
          have b4e350963 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e350940 X0 X1
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e350940
            | (have j0 := b4e350940 X0 X1
               grind)
            | exact resolve b4e350940 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e350940
          have b4e350967 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e350963 X0 X1
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e350963
            | (have j0 := b4e350963 X0 X1
               grind)
            | exact resolve b4e350963 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72 b4e350963
          have b4e350971 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e350967 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e350967
            | (have j0 := b4e350967 X0 X1
               grind)
            | exact resolve b4e350967 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e350967
          have b4e724214 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (σ (M.op y y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e109023 y x
               grind)
            | exact superpose b4e109023 b4e20
            | (have j1 := b4e109023 y x
               grind)
            | exact resolve b4e20 b4e109023
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109023
          have b4e724219 : (σ (M.op y y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
            first
            | (have j1 := b4e343175 y x
               grind)
            | (have r₁ := b4e724214
               have r₂ := b4e343175 y x
               grind)
            | exact resolve b4e724214 b4e343175
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e343175 b4e724214
          have b4e730915 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e350971 x y
               have i₂ := b4e724219
               grind)
            | exact superpose b4e724219 b4e350971
            | (have j0 := b4e350971 x y
               grind)
            | exact resolve b4e350971 b4e724219
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e350971
          have b4e730917 : (k y x) = (τ (σ (M.op y y))) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e724219
               grind)
            | exact superpose b4e724219 b4e14
            | exact resolve b4e14 b4e724219
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e724219
          have b4e730938 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (k y x) := by grind
          clear b4e730915
          have b4e730962 : (M.op y y) = (k y x) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e730917
               have i₂ := b4e14 (M.op y y)
               grind)
            | exact superpose b4e14 b4e730917
            | exact resolve b4e730917 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e730917
          have b4e730963 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (k y x) := by
            first
            | (have r₁ := b4e730938
               have r₂ := b4e153
               grind)
            | exact resolve b4e730938 b4e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e153 b4e730938
          have b4e739003 : (M.op x y) ≠ (M.op y y) ∨ (M.op x y) = (k y x) := by grind
          clear b4e730962
          have b4e2607268 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e113293 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e113293
            | (have j0 := b4e113293 X1 (σ X0)
               grind)
            | exact resolve b4e113293 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e113293
          have b4e2608420 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e15 (M.op (σ X0) (σ X1))
               have i₂ := b4e2607268 X1 X0
               grind)
            | exact superpose b4e2607268 b4e15
            | (have j1 := b4e2607268 X1 X0
               grind)
            | exact resolve b4e15 b4e2607268
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2607268
          have b4e2609076 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e2608420 x y
               grind)
            | exact superpose b4e2608420 b4e20
            | (have j1 := b4e2608420 x y
               grind)
            | (have r₁ := b4e20
               have r₂ := b4e2608420 x y
               grind)
            | exact resolve b4e20 b4e2608420
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2608420
          have b4e2609079 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by grind
          clear b4e2609076
          have b4e2609084 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e2609079
               grind)
            | exact superpose b4e2609079 b4e20
            | exact resolve b4e20 b4e2609079
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2609079
          have b4e2609097 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e2609084
               have i₂ := b4e730963
               grind)
            | exact superpose b4e730963 b4e2609084
            | (have r₁ := b4e2609084
               have r₂ := b4e730963
               grind)
            | exact resolve b4e2609084 b4e730963
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e730963 b4e2609084
          have b4e2609098 : (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by grind
          clear b4e2609097
          have b4e2609105 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e2609098
               have i₂ := b4e125 x y
               grind)
            | exact superpose b4e125 b4e2609098
            | (have j1 := b4e125 x y
               grind)
            | exact resolve b4e2609098 b4e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e125
          have b4e2609140 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k y x) := by grind
          clear b4e2609098
          have b4e2609142 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
          clear b4e2609105
          have b4e2609148 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
            first
            | (have j1 := b4e119 x y
               grind)
            | (have r₁ := b4e2609142
               have r₂ := b4e119 y x
               grind)
            | (have r₁ := b4e2609142
               have r₂ := b4e119 x y
               grind)
            | exact resolve b4e2609142 b4e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e119 b4e2609142
          have b4e2609152 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b4e2609148
               have r₂ := b4e739003
               grind)
            | exact resolve b4e2609148 b4e739003
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e739003 b4e2609148
          have b4e2609670 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e13888 y x
               have i₂ := b4e2609152
               grind)
            | exact superpose b4e2609152 b4e13888
            | (have j0 := b4e13888 y x
               grind)
            | exact resolve b4e13888 b4e2609152
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13888
          have b4e2609702 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b4e2609670
          have b4e2609713 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b4e2609702
               have r₂ := b4e144579
               grind)
            | exact resolve b4e2609702 b4e144579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e144579 b4e2609702
          have b4e2609718 : (M.op x y) ≠ (M.op x x) := by
            first
            | (have i₁ := b4e26
               have i₂ := b4e2609713
               grind)
            | exact superpose b4e2609713 b4e26
            | exact resolve b4e26 b4e2609713
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e2609797 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e17 y X0
               have i₂ := b4e2609713
               grind)
            | exact superpose b4e2609713 b4e17
            | (have j0 := b4e17 y X0
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e2609713
               grind)
            | exact resolve b4e17 b4e2609713
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2609713
          have b4e2611222 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j0 := b4e2609797 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2609797
          have b4e2611223 : (M.op x x) = (k y x) := by
            first
            | (have r₁ := b4e2611222
               have r₂ := b4e2609140
               grind)
            | exact resolve b4e2611222 b4e2609140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2609140 b4e2611222
          have b4e2611347 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e2609152
               have i₂ := b4e2611223
               grind)
            | exact superpose b4e2611223 b4e2609152
            | exact resolve b4e2609152 b4e2611223
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2609152 b4e2611223
          have b4e2611382 : False := by grind
          exact b4e2611382
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b5e22 : (M.op y x) = (M.op x x) := by grind
          have b5e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op y y) ≠ (M.op x x) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e60 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e60 (σ X0)
               grind)
            | exact superpose b5e60 b5e19
            | exact resolve b5e19 b5e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e62 X0
               have i₂ := b5e60 X0
               grind)
            | exact superpose b5e60 b5e62
            | exact resolve b5e62 b5e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60 b5e62
          have b5e79 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by
            first
            | (have i₁ := b5e17 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 x x
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e82 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
          clear b5e79
          have b5e83 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b5e82
               have r₂ := b5e25
               grind)
            | exact resolve b5e82 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e82
          have b5e97 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ y) (σ y)
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e136 : (M.op (σ y) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e71 y
               grind)
            | exact superpose b5e71 b5e23
            | exact resolve b5e23 b5e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71
          have b5e693 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e97 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e97
          have b5e694 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e693
               have r₂ := b5e24
               grind)
            | exact resolve b5e693 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e693
          have b5e695 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e694
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e694
            | exact resolve b5e694 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e694
          have b5e696 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e695
               have i₂ := b5e83
               grind)
            | exact superpose b5e83 b5e695
            | exact resolve b5e695 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83 b5e695
          have b5e697 : False := by grind
          exact b5e697
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op y x) ≠ (M.op y y) := by grind
        have b6e21 : (M.op y x) ≠ (M.op x x) := by grind
        have b6e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e45 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ y) (σ y)
             grind)
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e47 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e45
        have b6e48 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e47
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e47
          | exact resolve b6e47 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47
        have b6e68 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e48
             grind)
          | exact superpose b6e48 b6e15
          | exact resolve b6e15 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48
        have b6e69 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e68
        have b6e70 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e69
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e69
          | exact resolve b6e69 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e71 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e70
             have i₂ := b6e46 x
             grind)
          | exact superpose b6e46 b6e70
          | exact resolve b6e70 b6e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46 b6e70
        have b6e123 : (k x y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e71
             grind)
          | exact superpose b6e71 b6e13
          | exact resolve b6e13 b6e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e124 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b6e123
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e123
          | exact resolve b6e123 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e123
        have b6e144 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e124
             grind)
          | exact superpose b6e124 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e124
        have b6e145 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) := by grind
        clear b6e144
        have b6e147 : (M.op y x) = (M.op y y) := by
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b7e22 : (M.op y x) ≠ (M.op x x) := by grind
          have b7e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e60 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e60 (σ X0)
               grind)
            | exact superpose b7e60 b7e19
            | exact resolve b7e19 b7e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e62 X0
               have i₂ := b7e60 X0
               grind)
            | exact superpose b7e60 b7e62
            | exact resolve b7e62 b7e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60 b7e62
          have b7e80 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) (σ x)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e82 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e80
          have b7e83 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e82
               have r₂ := b7e25
               grind)
            | exact resolve b7e82 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e82
          have b7e84 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e83
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e83
            | exact resolve b7e83 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e85 : (σ (k x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e84
               have i₂ := b7e71 y
               grind)
            | exact superpose b7e71 b7e84
            | exact resolve b7e84 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71 b7e84
          have b7e90 : (k x y) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e85
               grind)
            | exact superpose b7e85 b7e14
            | exact resolve b7e14 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e91 : (M.op y y) = (k x y) := by
            first
            | (have i₁ := b7e90
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e90
            | exact resolve b7e90 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e145 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e91
               grind)
            | exact superpose b7e91 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e146 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by grind
          clear b7e145
          have b7e148 : (M.op y x) = (M.op x x) := by
            first
            | (have r₁ := b7e146
               have r₂ := b7e21
               grind)
            | exact resolve b7e146 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e146
          have b7e150 : False := by grind
          exact b7e150
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e36 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b8e39 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          have b8e59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e59 (σ X0)
               grind)
            | exact superpose b8e59 b8e19
            | exact resolve b8e19 b8e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e64 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 (τ X0)
               have i₂ := b8e59 (τ X0)
               grind)
            | exact superpose b8e59 b8e26
            | exact resolve b8e26 b8e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e67 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e64 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e64
            | exact resolve b8e64 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e61 X0
               have i₂ := b8e59 X0
               grind)
            | exact superpose b8e59 b8e61
            | exact resolve b8e61 b8e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e73 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e67 X0
               have i₂ := b8e59 X0
               grind)
            | exact superpose b8e59 b8e67
            | exact resolve b8e67 b8e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59 b8e67
          have b8e85 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 (σ X0)
               have i₂ := b8e70 X0
               grind)
            | exact superpose b8e70 b8e16
            | (have j0 := b8e16 X1 (σ X0)
               grind)
            | exact resolve b8e16 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e113 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e17 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e17
            | (have j0 := b8e17 X0 X1
               have j1 := b8e18 X0 X1
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
          have b8e116 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
          have b8e118 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) (τ X1)) := by
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
          have b8e122 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e123 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e113 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113
          have b8e129 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e116 X0 X1
               have i₂ := b8e70 X0
               grind)
            | exact superpose b8e70 b8e116
            | (have j0 := b8e116 X0 X1
               grind)
            | exact resolve b8e116 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e116
          have b8e131 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e123 X0 X1
               have j1 := b8e122 X1 X0
               grind)
            | (have r₁ := b8e123 X0 X1
               have r₂ := b8e122 X0 X1
               grind)
            | (have r₁ := b8e123 X1 X0
               have r₂ := b8e122 X0 X1
               grind)
            | (have r₁ := b8e123 X1 X1
               have r₂ := b8e122 X1 X1
               grind)
            | exact resolve b8e123 b8e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e122 b8e123
          have b8e135 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e129 X0 X1
               have i₂ := b8e70 X1
               grind)
            | exact superpose b8e70 b8e129
            | (have j0 := b8e129 X0 X1
               grind)
            | exact resolve b8e129 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e129
          have b8e147 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e14
            | exact resolve b8e14 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e269 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 (τ X0)
               have i₂ := b8e147 X0
               grind)
            | exact superpose b8e147 b8e16
            | (have j0 := b8e16 X1 (τ X0)
               grind)
            | exact resolve b8e16 b8e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e381 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e131 X1 (τ X0)
               grind)
            | exact superpose b8e131 b8e26
            | (have j1 := b8e131 X1 (τ X0)
               grind)
            | exact resolve b8e26 b8e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e131
          have b8e405 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e381 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e381
            | (have j0 := b8e381 X0 X1
               grind)
            | exact resolve b8e381 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e381
          have b8e429 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e405 X0 X1
               have i₂ := b8e147 X0
               grind)
            | exact superpose b8e147 b8e405
            | (have j0 := b8e405 X0 X1
               grind)
            | exact resolve b8e405 b8e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147 b8e405
          have b8e1042 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X0) (σ X1)
               have i₂ := b8e135 X1 X0
               grind)
            | exact superpose b8e135 b8e16
            | (have j0 := b8e16 (σ X0) (σ X1)
               have j1 := b8e135 X1 X0
               grind)
            | exact resolve b8e16 b8e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e135
          have b8e1100 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e1042 X0 X1
               have j1 := b8e85 X1 (σ X0)
               grind)
            | (have r₁ := b8e1042 X0 X0
               have r₂ := b8e85 X0 (σ X0)
               grind)
            | (have r₁ := b8e1042 X0 X0
               have r₂ := b8e85 X0 (σ X0)
               grind)
            | exact resolve b8e1042 b8e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85 b8e1042
          have b8e1153 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1100 X0 X1
               have i₂ := b8e70 X1
               grind)
            | exact superpose b8e70 b8e1100
            | (have j0 := b8e1100 X0 X1
               grind)
            | exact resolve b8e1100 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1100
          have b8e1188 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1153 X0 X1
               have i₂ := b8e70 X0
               grind)
            | exact superpose b8e70 b8e1153
            | (have j0 := b8e1153 X0 X1
               grind)
            | exact resolve b8e1153 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1153
          have b8e1209 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1188 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e1188
            | (have j0 := b8e1188 X0 X1
               grind)
            | exact resolve b8e1188 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1188
          have b8e6474 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e269 X0 X1
               have i₂ := b8e429 X0 X1
               grind)
            | exact superpose b8e429 b8e269
            | (have j0 := b8e269 X0 X1
               have j1 := b8e429 X0 X1
               grind)
            | (have r₁ := b8e269 X0 X1
               have r₂ := b8e429 X0 X1
               grind)
            | exact resolve b8e269 b8e429
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e269 b8e429
          have b8e6643 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b8e6474 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6474
          have b8e7076 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e118 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e118
            | exact resolve b8e118 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e118
          have b8e7499 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e7076 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e7076
            | (have j0 := b8e7076 X0 X1
               grind)
            | exact resolve b8e7076 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7076
          have b8e11174 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1209 (τ X1) (τ X0)
               have i₂ := b8e39 X0 X1
               grind)
            | exact superpose b8e39 b8e1209
            | (have j0 := b8e1209 (τ X0) (τ X1)
               grind)
            | exact resolve b8e1209 b8e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1209
          have b8e11254 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e11174 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e11174
            | (have j0 := b8e11174 X0 X1
               grind)
            | exact resolve b8e11174 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11174
          have b8e11279 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e11254 X0 X1
               have i₂ := b8e73 X1
               grind)
            | exact superpose b8e73 b8e11254
            | (have j0 := b8e11254 X0 X1
               grind)
            | exact resolve b8e11254 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11254
          have b8e11300 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e11279 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e11279
            | (have j0 := b8e11279 X0 X1
               grind)
            | exact resolve b8e11279 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11279
          have b8e11311 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e11300 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e11300
            | (have j0 := b8e11300 X0 X1
               grind)
            | exact resolve b8e11300 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11300
          have b8e11318 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e11311 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e11311
            | (have j0 := b8e11311 X0 X1
               grind)
            | exact resolve b8e11311 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11311
          have b8e11321 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e11318 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e11318
            | (have j0 := b8e11318 X0 X1
               grind)
            | exact resolve b8e11318 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11318
          have b8e11322 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e11321 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e11321
            | (have j0 := b8e11321 X0 X1
               grind)
            | exact resolve b8e11321 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11321
          have b8e88319 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X0 (τ X1)
               have i₂ := b8e6643 X1 (τ X0)
               grind)
            | exact superpose b8e6643 b8e25
            | (have j1 := b8e6643 X1 (τ X0)
               grind)
            | exact resolve b8e25 b8e6643
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25
          have b8e88370 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 (σ X1) X0
               have i₂ := b8e6643 (σ X0) X1
               grind)
            | exact superpose b8e6643 b8e30
            | (have j1 := b8e6643 (σ X0) X1
               grind)
            | exact resolve b8e30 b8e6643
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6643
          have b8e88380 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e88370 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e88370
            | (have j0 := b8e88370 X0 X1
               grind)
            | exact resolve b8e88370 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88370
          have b8e88394 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e88319 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e88319
            | (have j0 := b8e88319 X0 X1
               grind)
            | exact resolve b8e88319 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73 b8e88319
          have b8e88421 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e88380 X0 X1
               have i₂ := b8e70 X0
               grind)
            | exact superpose b8e70 b8e88380
            | (have j0 := b8e88380 X0 X1
               grind)
            | exact resolve b8e88380 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88380
          have b8e88426 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e88394 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e88394
            | (have j0 := b8e88394 X0 X1
               grind)
            | exact resolve b8e88394 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88394
          have b8e88443 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e88421 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e88421
            | (have j0 := b8e88421 X0 X1
               grind)
            | exact resolve b8e88421 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88421
          have b8e88448 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e88426 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e88426
            | (have j0 := b8e88426 X0 X1
               grind)
            | exact resolve b8e88426 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88426
          have b8e88458 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e88443 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e88443
            | (have j0 := b8e88443 X0 X1
               grind)
            | exact resolve b8e88443 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88443
          have b8e88461 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e88448 X0 X1
               have i₂ := b8e39 X1 X0
               grind)
            | exact superpose b8e39 b8e88448
            | (have j0 := b8e88448 X0 X1
               grind)
            | exact resolve b8e88448 b8e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39 b8e88448
          have b8e88465 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e88458 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e88458
            | (have j0 := b8e88458 X0 X1
               grind)
            | exact resolve b8e88458 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88458
          have b8e89046 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X1 X0
               have i₂ := b8e88465 (σ X0) X1
               grind)
            | exact superpose b8e88465 b8e30
            | (have j1 := b8e88465 (σ X0) X1
               grind)
            | exact resolve b8e30 b8e88465
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e89089 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e88465 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88465
          have b8e89152 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e89046 X0 X1
               have i₂ := b8e70 X0
               grind)
            | exact superpose b8e70 b8e89046
            | (have j0 := b8e89046 X0 X1
               grind)
            | exact resolve b8e89046 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89046
          have b8e89290 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e89152 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e89152
            | (have j0 := b8e89152 X0 X1
               grind)
            | exact resolve b8e89152 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89152
          have b8e89625 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e89089 X0 X1
               have i₂ := b8e7499 X0 X1
               grind)
            | (have i₁ := b8e89089 X0 X0
               have i₂ := b8e7499 X0 X1
               grind)
            | exact superpose b8e7499 b8e89089
            | (have j0 := b8e89089 X0 X1
               have j1 := b8e7499 X0 X1
               grind)
            | (have r₁ := b8e89089 X0 X1
               have r₂ := b8e7499 X0 X1
               grind)
            | (have r₁ := b8e89089 X0 X0
               have r₂ := b8e7499 X0 X0
               grind)
            | exact resolve b8e89089 b8e7499
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7499 b8e89089
          have b8e89635 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e89625 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89625
          have b8e89665 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e89635 X0 X1
               have j1 := b8e16 X0 X1
               grind)
            | (have r₁ := b8e89635 X0 X1
               have r₂ := b8e16 X0 X1
               grind)
            | (have r₁ := b8e89635 X0 X0
               have r₂ := b8e16 X0 X0
               grind)
            | exact resolve b8e89635 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89635
          have b8e95217 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e88461 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e88461
            | (have j1 := b8e18 X1 X0
               grind)
            | exact resolve b8e88461 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e95296 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e11322 X0 X1
               have i₂ := b8e88461 X0 X1
               grind)
            | exact superpose b8e88461 b8e11322
            | (have j0 := b8e11322 X1 X0
               have j1 := b8e88461 X1 X0
               grind)
            | (have r₁ := b8e11322 X0 X1
               have r₂ := b8e88461 X0 X1
               grind)
            | (have r₁ := b8e11322 X1 X1
               have r₂ := b8e88461 X1 X1
               grind)
            | exact resolve b8e11322 b8e88461
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11322
          have b8e95383 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e88461 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88461
          have b8e95397 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e95296 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e95296
          have b8e95426 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e95217 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e95217
          have b8e95475 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e95397 X0 X1
               have j1 := b8e95383 X1 X0
               grind)
            | (have r₁ := b8e95397 X0 X1
               have r₂ := b8e95383 X0 X1
               grind)
            | (have r₁ := b8e95397 X1 X0
               have r₂ := b8e95383 X0 X1
               grind)
            | (have r₁ := b8e95397 X1 X1
               have r₂ := b8e95383 X1 X1
               grind)
            | exact resolve b8e95397 b8e95383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e95383 b8e95397
          have b8e99672 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X1 X1
               have i₂ := b8e95426 X0 X1
               grind)
            | (have i₁ := b8e17 X1 X0
               have i₂ := b8e95426 X0 X1
               grind)
            | exact superpose b8e95426 b8e17
            | (have j0 := b8e17 X0 X1
               have j1 := b8e95426 X1 X0
               grind)
            | (have r₁ := b8e17 X1 X0
               have r₂ := b8e95426 X0 X1
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e95426 X1 X1
               grind)
            | exact resolve b8e17 b8e95426
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e99724 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (M.op (σ X0) X1) ∨ (τ (M.op (σ X0) X1)) = (M.op (τ (σ X0)) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e70 X0
               have i₂ := b8e95426 (σ X0) X1
               grind)
            | (have i₁ := b8e70 X0
               have i₂ := b8e95426 (σ X0) (σ X0)
               grind)
            | exact superpose b8e95426 b8e70
            | (have j1 := b8e95426 (σ X0) X1
               grind)
            | exact resolve b8e70 b8e95426
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e99735 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e95426 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e95426
          have b8e99746 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e99672 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99672
          have b8e99757 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e99724 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e99724
            | (have j0 := b8e99724 X0 X1
               grind)
            | exact resolve b8e99724 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99724
          have b8e99768 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e99746 X0 X1
               have j1 := b8e99735 X1 X0
               grind)
            | (have r₁ := b8e99746 X0 X1
               have r₂ := b8e99735 X0 X1
               grind)
            | (have r₁ := b8e99746 X1 X0
               have r₂ := b8e99735 X0 X1
               grind)
            | (have r₁ := b8e99746 X1 X1
               have r₂ := b8e99735 X1 X1
               grind)
            | exact resolve b8e99746 b8e99735
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99735 b8e99746
          have b8e110550 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e95475 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e95475
            | (have j0 := b8e95475 (σ X0) X1
               grind)
            | exact resolve b8e95475 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e95475
          have b8e110615 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e110550 X0 X1
               have i₂ := b8e30 X1 X0
               grind)
            | exact superpose b8e30 b8e110550
            | (have j0 := b8e110550 X0 X1
               grind)
            | exact resolve b8e110550 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110550
          have b8e111835 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (τ (M.op (σ X0) X1)) = (M.op (τ (σ X0)) (τ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X1 X0
               have i₂ := b8e99768 X1 (σ X0)
               grind)
            | exact superpose b8e99768 b8e30
            | (have j1 := b8e99768 X1 (σ X0)
               grind)
            | exact resolve b8e30 b8e99768
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e99768
          have b8e111859 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (τ (M.op (σ X0) X1)) = (M.op (τ (σ X0)) (τ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e111835 X0 X1
               have i₂ := b8e70 X0
               grind)
            | exact superpose b8e70 b8e111835
            | (have j0 := b8e111835 X0 X1
               grind)
            | exact resolve b8e111835 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e111835
          have b8e111873 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ X1) X0) ∨ (τ (M.op (σ X0) X1)) = (M.op (τ (σ X0)) (τ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e111859 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e111859
            | (have j0 := b8e111859 X0 X1
               grind)
            | exact resolve b8e111859 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e111859
          have b8e111882 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e111873 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e111873
            | (have j0 := b8e111873 X0 X1
               grind)
            | exact resolve b8e111873 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e111873
          have b8e111886 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X0 X0) = (k (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e111882 X0 X1
               have i₂ := b8e70 X0
               grind)
            | exact superpose b8e70 b8e111882
            | (have j0 := b8e111882 X0 X1
               grind)
            | exact resolve b8e111882 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e111882
          have b8e158770 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e36 X0 (σ X1)
               have i₂ := b8e89290 X1 (σ X0)
               grind)
            | exact superpose b8e89290 b8e36
            | (have j1 := b8e89290 X1 (σ X0)
               grind)
            | exact resolve b8e36 b8e89290
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89290
          have b8e158830 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e158770 X0 X1
               have i₂ := b8e70 X0
               grind)
            | exact superpose b8e70 b8e158770
            | (have j0 := b8e158770 X0 X1
               grind)
            | exact resolve b8e158770 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158770
          have b8e158858 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e158830 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e158830
            | (have j0 := b8e158830 X0 X1
               grind)
            | exact resolve b8e158830 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158830
          have b8e158875 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e158858 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e158858
            | (have j0 := b8e158858 X0 X1
               grind)
            | exact resolve b8e158858 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158858
          have b8e158888 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e158875 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e158875
            | (have j0 := b8e158875 X0 X1
               grind)
            | exact resolve b8e158875 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158875
          have b8e158893 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e158888 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e158888
            | (have j0 := b8e158888 X0 X1
               grind)
            | exact resolve b8e158888 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158888
          have b8e168262 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e158893 y x
               grind)
            | exact superpose b8e158893 b8e20
            | (have j1 := b8e158893 y x
               grind)
            | exact resolve b8e20 b8e158893
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158893
          have b8e168396 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j1 := b8e89665 y x
               grind)
            | (have r₁ := b8e168262
               have r₂ := b8e89665 y x
               grind)
            | exact resolve b8e168262 b8e89665
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89665 b8e168262
          have b8e171346 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e168396
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e168396
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e168396 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e168396
          have b8e171388 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e171346
          have b8e176927 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) ∨ (M.op x y) = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b8e17 y X0
               have i₂ := b8e171388
               grind)
            | exact superpose b8e171388 b8e17
            | (have j0 := b8e17 y X0
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e171388
               grind)
            | exact resolve b8e17 b8e171388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e209289 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e36 X0 (σ X1)
               have i₂ := b8e110615 X1 (σ X0)
               grind)
            | exact superpose b8e110615 b8e36
            | (have j1 := b8e110615 X1 (σ X0)
               grind)
            | exact resolve b8e36 b8e110615
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36 b8e110615
          have b8e209294 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e209289 X0 X1
               have i₂ := b8e70 X0
               grind)
            | exact superpose b8e70 b8e209289
            | (have j0 := b8e209289 X0 X1
               grind)
            | exact resolve b8e209289 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e209289
          have b8e209313 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e209294 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e209294
            | (have j0 := b8e209294 X0 X1
               grind)
            | exact resolve b8e209294 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e209294
          have b8e209324 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e209313 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e209313
            | (have j0 := b8e209313 X0 X1
               grind)
            | exact resolve b8e209313 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e209313
          have b8e209330 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e209324 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e209324
            | (have j0 := b8e209324 X0 X1
               grind)
            | exact resolve b8e209324 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e209324
          have b8e209331 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e209330 X0 X1
               have i₂ := b8e70 X0
               grind)
            | exact superpose b8e70 b8e209330
            | (have j0 := b8e209330 X0 X1
               grind)
            | exact resolve b8e209330 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e209330
          have b8e212355 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e209331 y x
               grind)
            | exact superpose b8e209331 b8e20
            | (have j1 := b8e209331 y x
               grind)
            | exact resolve b8e20 b8e209331
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e209331
          have b8e214728 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e212355
               have i₂ := b8e171388
               grind)
            | exact superpose b8e171388 b8e212355
            | exact resolve b8e212355 b8e171388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e171388 b8e212355
          have b8e214731 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e214728
          have b8e214732 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e214731
          have b8e2601868 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op (σ X0) X1)) ∨ (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (M.op X0 X0)
               have i₂ := b8e99757 X0 X1
               grind)
            | exact superpose b8e99757 b8e14
            | (have j1 := b8e99757 X0 X1
               grind)
            | exact resolve b8e14 b8e99757
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99757
          have b8e2602480 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e111886 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e111886
            | (have j0 := b8e111886 X1 (σ X0)
               grind)
            | exact resolve b8e111886 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e111886
          have b8e2602908 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b8e2601868 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2601868
          have b8e2602929 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e2602908 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e2602908
            | (have j0 := b8e2602908 X1 (σ X0)
               grind)
            | exact resolve b8e2602908 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2602908
          have b8e2602934 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (τ (M.op (σ X1) (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e2602929 X0 X1
               have i₂ := b8e70 X0
               grind)
            | exact superpose b8e70 b8e2602929
            | (have j0 := b8e2602929 X0 X1
               grind)
            | exact resolve b8e2602929 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70 b8e2602929
          have b8e2603740 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e15 (M.op (σ X0) (σ X1))
               have i₂ := b8e2602480 X1 X0
               grind)
            | exact superpose b8e2602480 b8e15
            | (have j1 := b8e2602480 X1 X0
               grind)
            | exact resolve b8e15 b8e2602480
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2602480
          have b8e2604203 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2603740 x y
               grind)
            | exact superpose b8e2603740 b8e20
            | (have j1 := b8e2603740 x y
               grind)
            | (have r₁ := b8e20
               have r₂ := b8e2603740 x y
               grind)
            | exact resolve b8e20 b8e2603740
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2603740
          have b8e2604206 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by grind
          clear b8e2604203
          have b8e2604215 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2604206
               grind)
            | exact superpose b8e2604206 b8e20
            | exact resolve b8e20 b8e2604206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2604206
          have b8e2606381 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have j0 := b8e176927 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e176927
          have b8e2606382 : (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e2606381
          have b8e2606400 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e214732
               have i₂ := b8e2606382
               grind)
            | exact superpose b8e2606382 b8e214732
            | exact resolve b8e214732 b8e2606382
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e214732 b8e2606382
          have b8e2606447 : (M.op x y) = (M.op x x) := by grind
          clear b8e2606400
          have b8e2606457 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e2604215
               have i₂ := b8e2606447
               grind)
            | exact superpose b8e2606447 b8e2604215
            | exact resolve b8e2604215 b8e2606447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2604215
          have b8e2606458 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e2606447
               grind)
            | exact superpose b8e2606447 b8e16
            | (have j0 := b8e16 x x
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e2606447
               grind)
            | exact resolve b8e16 b8e2606447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2606492 : (M.op x x) ≠ (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x x) = (τ (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b8e2602934 y x
               have i₂ := b8e2606447
               grind)
            | exact superpose b8e2606447 b8e2602934
            | (have j0 := b8e2602934 x x
               grind)
            | (have r₁ := b8e2602934 y x
               have r₂ := b8e2606447
               grind)
            | exact resolve b8e2602934 b8e2606447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2602934
          have b8e2606511 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
          clear b8e2606492
          have b8e2606533 : (M.op y y) = (k y x) := by grind
          clear b8e2606458
          have b8e2606534 : (M.op x x) = (k y x) := by grind
          clear b8e2606457
          have b8e2607015 : (M.op y y) = (M.op x x) := by
            first
            | (have i₁ := b8e2606533
               have i₂ := b8e2606534
               grind)
            | exact superpose b8e2606534 b8e2606533
            | exact resolve b8e2606533 b8e2606534
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2606533 b8e2606534
          have b8e2608716 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e15 (M.op (σ x) (σ y))
               have i₂ := b8e2606511
               grind)
            | exact superpose b8e2606511 b8e15
            | exact resolve b8e15 b8e2606511
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2606511
          have b8e2608725 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e2608716
               have i₂ := b8e2607015
               grind)
            | exact superpose b8e2607015 b8e2608716
            | exact resolve b8e2608716 b8e2607015
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2607015 b8e2608716
          have b8e2608726 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
          clear b8e2608725
          have b8e2608750 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2608726
               grind)
            | exact superpose b8e2608726 b8e20
            | exact resolve b8e20 b8e2608726
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2608726
          have b8e2608821 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e2608750
               have i₂ := b8e2606447
               grind)
            | exact superpose b8e2606447 b8e2608750
            | exact resolve b8e2608750 b8e2606447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2606447 b8e2608750
          have b8e2608822 : False := by grind
          exact b8e2608822

/-- `Equation317`: `x ◇ x = y ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pxy_x_y_pxy_Equation317 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law317 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law317.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X4)) := by
          intro X0 X1 X3 X4
          first
          | (have i₁ := b1e12 x X3 X4
             have i₂ := b1e12 x X0 X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X1 X2 (M.op X2 x)
             have i₂ := b1e12 X0 X2 x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 x x
             have i₂ := b1e12 X1 x x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : ∀ X0 : G, (M.op X0 X0) = y := by
          intro X0
          first
          | (have i₁ := b1e27 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e27
          | exact resolve b1e27 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e33 : y ≠ y ∨ x = (k x y) := by
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
        have b1e36 : x = (k x y) := by grind
        clear b1e33
        have b1e39 : y ≠ (σ y) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e32 (σ x)
             grind)
          | exact superpose b1e32 b1e23
          | exact resolve b1e23 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 X1
             have i₂ := b1e32 X1
             grind)
          | exact superpose b1e32 b1e12
          | exact resolve b1e12 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : ∀ X1 : G, y = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b1e42 x X1
             have i₂ := b1e32 x
             grind)
          | exact superpose b1e32 b1e42
          | exact resolve b1e42 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e45 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e18
          | exact resolve b1e18 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e53 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e16 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) (σ x)
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e53
        have b1e59 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e55
             have r₂ := b1e23
             grind)
          | exact resolve b1e55 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e55
        have b1e64 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e59
          | exact resolve b1e59 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e66 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e64
             have i₂ := b1e36
             grind)
          | exact superpose b1e36 b1e64
          | exact resolve b1e64 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36 b1e64
        have b1e102 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e66
             grind)
          | exact superpose b1e66 b1e13
          | exact resolve b1e13 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66
        have b1e103 : x = y := by
          first
          | (have i₁ := b1e102
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e102
          | exact resolve b1e102 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e102
        have b1e145 : x ≠ (σ x) := by
          first
          | (have i₁ := b1e39
             have i₂ := b1e103
             grind)
          | exact superpose b1e103 b1e39
          | exact resolve b1e39 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e208 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X1 X1) X2) ∨ (M.op (M.op X1 X1) X2) = X2 ∨ (k (M.op X1 X1) X2) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e16 (M.op X1 X1) X2
             have i₂ := b1e29 X1 X0 (M.op X1 X1)
             grind)
          | (have i₁ := b1e16 X1 X1
             have i₂ := b1e29 X0 X1 X2
             grind)
          | exact superpose b1e29 b1e16
          | (have j0 := b1e16 (M.op X1 X1) X2
             grind)
          | (have r₁ := b1e16 X2 (M.op X0 X0)
             have r₂ := b1e29 X0 X2 X2
             grind)
          | (have r₁ := b1e16 (M.op X0 X0) (M.op X0 X0)
             have r₂ := b1e29 X0 (M.op X0 X0) (M.op X0 X0)
             grind)
          | exact resolve b1e16 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e209 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) X2) ∨ (M.op (M.op X1 X1) X2) = (k (M.op X1 X1) X2) ∨ (M.op (M.op X1 X1) X2) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e17 (M.op X1 X1) X2
             have i₂ := b1e29 X1 X0 (M.op X1 X1)
             grind)
          | (have i₁ := b1e17 X1 X1
             have i₂ := b1e29 X0 X1 X2
             grind)
          | exact superpose b1e29 b1e17
          | (have j0 := b1e17 (M.op X1 X1) X2
             grind)
          | exact resolve b1e17 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e216 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (k X1 (M.op X2 X2)) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e15 X1 (M.op X2 X2)
             have i₂ := b1e29 X2 X0 X1
             grind)
          | (have i₁ := b1e15 X1 X1
             have i₂ := b1e29 X0 X1 X2
             grind)
          | exact superpose b1e29 b1e15
          | (have j0 := b1e15 X1 (M.op X2 X2)
             grind)
          | (have r₁ := b1e15 (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X0 X0))
             have r₂ := b1e29 X0 (M.op X2 (M.op X0 X0)) X2
             grind)
          | (have r₁ := b1e15 X2 (M.op X1 X1)
             have r₂ := b1e29 X1 X1 X2
             grind)
          | exact resolve b1e15 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e219 : ∀ X1 X2 : G, (k X1 (M.op X2 X2)) = X1 := by
          intro X1 X2
          first
          | (have j0 := b1e216 x X1 X2
             grind)
          | (have r₁ := b1e216 x X1 X1
             have r₂ := b1e30 x X1
             grind)
          | (have r₁ := b1e216 X1 X1 x
             have r₂ := b1e30 x X1
             grind)
          | exact resolve b1e216 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e216
        have b1e221 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op y X2) ∨ (M.op (M.op X1 X1) X2) = (k (M.op X1 X1) X2) ∨ (M.op (M.op X1 X1) X2) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e209 X0 X1 X2
             have i₂ := b1e32 X1
             grind)
          | exact superpose b1e32 b1e209
          | (have j0 := b1e209 X0 X1 X2
             grind)
          | exact resolve b1e209 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e209
        have b1e222 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op y X2) ∨ (M.op (M.op X1 X1) X2) = X2 ∨ (k (M.op X1 X1) X2) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e208 X0 X1 X2
             have i₂ := b1e32 X1
             grind)
          | exact superpose b1e32 b1e208
          | (have j0 := b1e208 X0 X1 X2
             grind)
          | exact resolve b1e208 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e208
        have b1e239 : ∀ X1 : G, (k X1 y) = X1 := by
          intro X1
          first
          | (have i₁ := b1e219 X1 x
             have i₂ := b1e32 x
             grind)
          | exact superpose b1e32 b1e219
          | exact resolve b1e219 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e219
        have b1e241 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op x X2) ∨ (M.op (M.op X1 X1) X2) = (k (M.op X1 X1) X2) ∨ (M.op (M.op X1 X1) X2) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e221 X0 X1 X2
             have i₂ := b1e103
             grind)
          | exact superpose b1e103 b1e221
          | (have j0 := b1e221 X0 X1 X2
             grind)
          | exact resolve b1e221 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e221
        have b1e242 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op x X2) ∨ (M.op (M.op X1 X1) X2) = X2 ∨ (k (M.op X1 X1) X2) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e222 X0 X1 X2
             have i₂ := b1e103
             grind)
          | exact superpose b1e103 b1e222
          | (have j0 := b1e222 X0 X1 X2
             grind)
          | exact resolve b1e222 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e222
        have b1e256 : ∀ X1 : G, (k X1 x) = X1 := by
          intro X1
          first
          | (have i₁ := b1e239 X1
             have i₂ := b1e103
             grind)
          | exact superpose b1e103 b1e239
          | exact resolve b1e239 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e239
        have b1e257 : ∀ X1 X2 : G, y = (M.op x X2) ∨ (M.op (M.op X1 X1) X2) = (k (M.op X1 X1) X2) ∨ (M.op (M.op X1 X1) X2) = X2 := by
          intro X1 X2
          first
          | (have i₁ := b1e241 x X1 X2
             have i₂ := b1e32 x
             grind)
          | exact superpose b1e32 b1e241
          | (have j0 := b1e241 x X1 X2
             grind)
          | exact resolve b1e241 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e241
        have b1e258 : ∀ X1 X2 : G, y ≠ (M.op x X2) ∨ (M.op (M.op X1 X1) X2) = X2 ∨ (k (M.op X1 X1) X2) = X2 := by
          intro X1 X2
          first
          | (have i₁ := b1e242 x X1 X2
             have i₂ := b1e32 x
             grind)
          | exact superpose b1e32 b1e242
          | (have j0 := b1e242 x X1 X2
             grind)
          | exact resolve b1e242 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e242
        have b1e264 : ∀ X1 X2 : G, x = (M.op x X2) ∨ (M.op (M.op X1 X1) X2) = (k (M.op X1 X1) X2) ∨ (M.op (M.op X1 X1) X2) = X2 := by
          intro X1 X2
          first
          | (have i₁ := b1e257 X1 X2
             have i₂ := b1e103
             grind)
          | exact superpose b1e103 b1e257
          | (have j0 := b1e257 X1 X2
             grind)
          | exact resolve b1e257 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e257
        have b1e265 : ∀ X1 X2 : G, x ≠ (M.op x X2) ∨ (M.op (M.op X1 X1) X2) = X2 ∨ (k (M.op X1 X1) X2) = X2 := by
          intro X1 X2
          first
          | (have i₁ := b1e258 X1 X2
             have i₂ := b1e103
             grind)
          | exact superpose b1e103 b1e258
          | (have j0 := b1e258 X1 X2
             grind)
          | exact resolve b1e258 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e258
        have b1e267 : ∀ X1 X2 : G, (M.op y X2) = (k y X2) ∨ x = (M.op x X2) ∨ (M.op (M.op X1 X1) X2) = X2 := by
          intro X1 X2
          first
          | (have i₁ := b1e264 x X2
             have i₂ := b1e32 x
             grind)
          | exact superpose b1e32 b1e264
          | (have j0 := b1e264 X1 X2
             grind)
          | exact resolve b1e264 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e264
        have b1e268 : ∀ X1 X2 : G, (M.op y X2) = X2 ∨ x ≠ (M.op x X2) ∨ (k (M.op X1 X1) X2) = X2 := by
          intro X1 X2
          first
          | (have i₁ := b1e265 X1 X2
             have i₂ := b1e32 X1
             grind)
          | exact superpose b1e32 b1e265
          | (have j0 := b1e265 X1 X2
             grind)
          | exact resolve b1e265 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e265
        have b1e270 : ∀ X1 X2 : G, (M.op x X2) = (k x X2) ∨ x = (M.op x X2) ∨ (M.op (M.op X1 X1) X2) = X2 := by
          intro X1 X2
          first
          | (have i₁ := b1e267 X1 X2
             have i₂ := b1e103
             grind)
          | exact superpose b1e103 b1e267
          | (have j0 := b1e267 X1 X2
             grind)
          | exact resolve b1e267 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e267
        have b1e271 : ∀ X1 X2 : G, (M.op x X2) = X2 ∨ x ≠ (M.op x X2) ∨ (k (M.op X1 X1) X2) = X2 := by
          intro X1 X2
          first
          | (have i₁ := b1e268 X1 X2
             have i₂ := b1e103
             grind)
          | exact superpose b1e103 b1e268
          | (have j0 := b1e268 X1 X2
             grind)
          | exact resolve b1e268 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e268
        have b1e273 : ∀ X2 : G, (M.op y X2) = X2 ∨ (M.op x X2) = (k x X2) ∨ x = (M.op x X2) := by
          intro X2
          first
          | (have i₁ := b1e270 x X2
             have i₂ := b1e32 x
             grind)
          | exact superpose b1e32 b1e270
          | (have j0 := b1e270 x X2
             grind)
          | exact resolve b1e270 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e270
        have b1e274 : ∀ X2 : G, (k y X2) = X2 ∨ (M.op x X2) = X2 ∨ x ≠ (M.op x X2) := by
          intro X2
          first
          | (have i₁ := b1e271 x X2
             have i₂ := b1e32 x
             grind)
          | exact superpose b1e32 b1e271
          | (have j0 := b1e271 x X2
             grind)
          | exact resolve b1e271 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32 b1e271
        have b1e276 : ∀ X2 : G, (M.op x X2) = (k x X2) ∨ (M.op x X2) = X2 ∨ x = (M.op x X2) := by
          intro X2
          first
          | (have i₁ := b1e273 X2
             have i₂ := b1e103
             grind)
          | exact superpose b1e103 b1e273
          | (have j0 := b1e273 X2
             grind)
          | exact resolve b1e273 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e273
        have b1e277 : ∀ X2 : G, x ≠ (M.op x X2) ∨ (M.op x X2) = X2 ∨ (k x X2) = X2 := by
          intro X2
          first
          | (have i₁ := b1e274 X2
             have i₂ := b1e103
             grind)
          | exact superpose b1e103 b1e274
          | (have j0 := b1e274 X2
             grind)
          | exact resolve b1e274 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e274
        have b1e288 : ∀ X0 : G, x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b1e43 x
             have i₂ := b1e103
             grind)
          | exact superpose b1e103 b1e43
          | exact resolve b1e43 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43 b1e103
        have b1e311 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e45 X1 X0
             grind)
          | exact superpose b1e45 b1e13
          | exact resolve b1e13 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e433 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 x) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e26 X0 X1 X2 x
             have i₂ := b1e288 X2
             grind)
          | exact superpose b1e288 b1e26
          | exact resolve b1e26 b1e288
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e437 : ∀ X0 X1 : G, x = (M.op X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e433 X0 X1 x
             have i₂ := b1e288 x
             grind)
          | exact superpose b1e288 b1e433
          | exact resolve b1e433 b1e288
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e288 b1e433
        have b1e1236 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ x)) := by
          intro X0
          first
          | (have i₁ := b1e311 X0 x
             have i₂ := b1e256 (σ X0)
             grind)
          | exact superpose b1e256 b1e311
          | exact resolve b1e311 b1e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e256 b1e311
        have b1e1244 : ∀ X0 : G, (k X0 (τ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e1236 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e1236
          | exact resolve b1e1236 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1236
        have b1e2186 : x = (M.op x (τ x)) ∨ (τ x) = (M.op x (τ x)) ∨ x = (M.op x (τ x)) := by
          first
          | (have i₁ := b1e1244 x
             have i₂ := b1e276 (τ x)
             grind)
          | exact superpose b1e276 b1e1244
          | (have j1 := b1e276 (τ x)
             grind)
          | exact resolve b1e1244 b1e276
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e276
        have b1e2197 : (τ x) = (M.op x (τ x)) ∨ x = (M.op x (τ x)) := by grind
        clear b1e2186
        have b1e2734 : x = (M.op x (τ x)) ∨ x = (M.op x (τ x)) := by
          first
          | (have i₁ := b1e437 x (τ x)
             have i₂ := b1e2197
             grind)
          | exact superpose b1e2197 b1e437
          | exact resolve b1e437 b1e2197
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e437 b1e2197
        have b1e2737 : x = (M.op x (τ x)) := by grind
        clear b1e2734
        have b1e2796 : x ≠ x ∨ x = (τ x) ∨ (τ x) = (k x (τ x)) := by
          first
          | (have i₁ := b1e277 (τ x)
             have i₂ := b1e2737
             grind)
          | exact superpose b1e2737 b1e277
          | (have j0 := b1e277 (τ x)
             grind)
          | (have r₁ := b1e277 (τ x)
             have r₂ := b1e2737
             grind)
          | exact resolve b1e277 b1e2737
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e277 b1e2737
        have b1e2817 : x = (τ x) ∨ (τ x) = (k x (τ x)) := by grind
        clear b1e2796
        have b1e2822 : x = (τ x) ∨ x = (τ x) := by
          first
          | (have i₁ := b1e2817
             have i₂ := b1e1244 x
             grind)
          | exact superpose b1e1244 b1e2817
          | exact resolve b1e2817 b1e1244
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1244 b1e2817
        have b1e2823 : x = (τ x) := by grind
        clear b1e2822
        have b1e2899 : x = (σ x) := by
          first
          | (have i₁ := b1e14 x
             have i₂ := b1e2823
             grind)
          | exact superpose b1e2823 b1e14
          | exact resolve b1e14 b1e2823
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2823
        have b1e2909 : False := by grind
        exact b1e2909
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
          intro X0
          first
          | (have i₁ := b2e12 X0 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 x x
             have i₂ := b2e12 X1 x x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 : G, (M.op X0 X0) = y := by
          intro X0
          first
          | (have i₁ := b2e25 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e25
          | exact resolve b2e25 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e38 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 X1
             have i₂ := b2e29 X1
             grind)
          | exact superpose b2e29 b2e12
          | exact resolve b2e12 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e39 : ∀ X1 : G, y = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b2e38 x X1
             have i₂ := b2e29 x
             grind)
          | exact superpose b2e29 b2e38
          | exact resolve b2e38 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38
        have b2e40 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e42 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e15 X0 y
             have i₂ := b2e39 X0
             grind)
          | exact superpose b2e39 b2e15
          | (have j0 := b2e15 X0 y
             grind)
          | (have r₁ := b2e15 x y
             have r₂ := b2e39 x
             grind)
          | exact resolve b2e15 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e44 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e42 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42
        have b2e46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ y ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X0 X1
             have i₂ := b2e29 X0
             grind)
          | exact superpose b2e29 b2e16
          | (have j0 := b2e16 X0 X1
             grind)
          | exact resolve b2e16 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e51 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X2) ∨ (M.op X1 X2) = (k X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e16 X1 (M.op X1 X2)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e16
          | (have j0 := b2e16 X1 (M.op X1 X2)
             grind)
          | (have r₁ := b2e16 X1 (M.op X1 X2)
             have r₂ := b2e12 X1 X1 X2
             grind)
          | exact resolve b2e16 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e56 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X2) ∨ (M.op X1 X2) = (k X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e51 X0 X1 X2
             grind)
          | (have r₁ := b2e51 X0 X1 X2
             have r₂ := b2e28 X0 X1
             grind)
          | (have r₁ := b2e51 X1 X0 X2
             have r₂ := b2e28 X0 X1
             grind)
          | exact resolve b2e51 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28 b2e51
        have b2e60 : ∀ X1 X2 : G, (M.op X1 X2) = (k X1 (M.op X1 X2)) ∨ (M.op X1 X2) = y := by
          intro X1 X2
          first
          | (have i₁ := b2e56 x X1 X2
             have i₂ := b2e29 x
             grind)
          | exact superpose b2e29 b2e56
          | (have j0 := b2e56 x X1 X2
             grind)
          | exact resolve b2e56 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ y = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e68 X0 X1
             have i₂ := b2e29 (σ X0)
             grind)
          | exact superpose b2e29 b2e68
          | (have j0 := b2e68 X0 X1
             grind)
          | exact resolve b2e68 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68
        have b2e244 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e40 X0 y
             have i₂ := b2e44 (τ X0)
             grind)
          | exact superpose b2e44 b2e40
          | exact resolve b2e40 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44
        have b2e247 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e40 X0 X1
             grind)
          | exact superpose b2e40 b2e13
          | exact resolve b2e13 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e248 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e244 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e244
          | exact resolve b2e244 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e244
        have b2e594 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e247 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e247
          | exact resolve b2e247 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e247
        have b2e818 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ y = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 (σ X0) (σ X1)
             have i₂ := b2e87 X0 X1
             grind)
          | exact superpose b2e87 b2e16
          | (have j0 := b2e16 (σ X0) (σ X1)
             have j1 := b2e87 X0 X1
             grind)
          | exact resolve b2e16 b2e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e828 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ y = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e87 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87
        have b2e833 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ y = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e818 X0 X1
             have j1 := b2e828 X0 X1
             grind)
          | (have r₁ := b2e818 X0 X1
             have r₂ := b2e828 X0 X1
             grind)
          | exact resolve b2e818 b2e828
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e818 b2e828
        have b2e844 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e833 X0 X1
             have j1 := b2e46 (σ X0) (σ X1)
             grind)
          | (have r₁ := b2e833 X0 X1
             have r₂ := b2e46 (σ X0) (σ X1)
             grind)
          | exact resolve b2e833 b2e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46 b2e833
        have b2e848 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ y ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e844 X0 X1
             have i₂ := b2e29 (σ X0)
             grind)
          | exact superpose b2e29 b2e844
          | (have j0 := b2e844 X0 X1
             grind)
          | exact resolve b2e844 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29 b2e844
        have b2e852 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ y ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e848 X0 X1
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e848
          | (have j0 := b2e848 X0 X1
             grind)
          | exact resolve b2e848 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e848
        have b2e2175 : ∀ X0 X1 : G, y ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e852 (τ X1) (τ X0)
             have i₂ := b2e594 X0 X1
             grind)
          | exact superpose b2e594 b2e852
          | (have j0 := b2e852 (τ X0) (τ X1)
             grind)
          | exact resolve b2e852 b2e594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e594 b2e852
        have b2e2184 : ∀ X0 X1 : G, (k X0 X1) ≠ y ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e2175 X0 X1
             have i₂ := b2e14 (k X0 X1)
             grind)
          | exact superpose b2e14 b2e2175
          | (have j0 := b2e2175 X0 X1
             grind)
          | exact resolve b2e2175 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2175
        have b2e2196 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ X1)) ∨ (k X0 X1) ≠ y ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e2184 X0 X1
             have i₂ := b2e14 (k X0 X1)
             grind)
          | exact superpose b2e14 b2e2184
          | (have j0 := b2e2184 X0 X1
             grind)
          | exact resolve b2e2184 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2184
        have b2e2205 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 X1) ≠ y ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e2196 X0 X1
             have i₂ := b2e14 X1
             grind)
          | exact superpose b2e14 b2e2196
          | (have j0 := b2e2196 X0 X1
             grind)
          | exact resolve b2e2196 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2196
        have b2e2206 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ y := by
          intro X0 X1
          first
          | (have i₁ := b2e2205 X0 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e2205
          | (have j0 := b2e2205 X0 X1
             grind)
          | exact resolve b2e2205 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2205
        have b2e2207 : ∀ X0 X1 : G, (k X0 X1) ≠ y ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e2206 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e2206
          | (have j0 := b2e2206 X0 X1
             grind)
          | exact resolve b2e2206 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2206
        have b2e3524 : ∀ X0 : G, y ≠ X0 ∨ (σ y) = X0 ∨ (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e2207 X0 (σ y)
             have i₂ := b2e248 X0
             grind)
          | exact superpose b2e248 b2e2207
          | (have j0 := b2e2207 X0 (σ y)
             grind)
          | (have r₁ := b2e2207 y (σ y)
             have r₂ := b2e248 y
             grind)
          | exact resolve b2e2207 b2e248
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2207
        have b2e3595 : (σ y) = (M.op y (σ y)) ∨ y = (σ y) := by
          first
          | (have j0 := b2e3524 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3524
        have b2e3893 : (σ y) = (k y (σ y)) ∨ y = (σ y) ∨ y = (σ y) := by
          first
          | (have i₁ := b2e60 y (σ y)
             have i₂ := b2e3595
             grind)
          | exact superpose b2e3595 b2e60
          | exact resolve b2e60 b2e3595
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60 b2e3595
        have b2e3894 : (σ y) = (k y (σ y)) ∨ y = (σ y) := by grind
        clear b2e3893
        have b2e3896 : y = (σ y) ∨ y = (σ y) := by
          first
          | (have i₁ := b2e3894
             have i₂ := b2e248 y
             grind)
          | exact superpose b2e248 b2e3894
          | exact resolve b2e3894 b2e248
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e248 b2e3894
        have b2e3897 : y = (σ y) := by grind
        clear b2e3896
        have b2e4237 : y ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e3897
             grind)
          | exact superpose b2e3897 b2e21
          | exact resolve b2e21 b2e3897
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3897
        have b2e4286 : False := by grind
        exact b2e4286
  · rcases eq_or_ne (M.op x x) (M.op x y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x y) := by grind
        have b3e21 : (M.op x y) = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : y ≠ (M.op x x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e28 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 X2 (M.op X2 x)
             have i₂ := b3e12 X0 X2 x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 x x
             have i₂ := b3e12 X1 x x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e28 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e28
          | exact resolve b3e28 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e34 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b3e37 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b3e34
        have b3e39 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b3e37
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e37
          | exact resolve b3e37 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e42 : y ≠ (σ y) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e32 x
             grind)
          | exact superpose b3e32 b3e23
          | exact resolve b3e23 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 X1
             have i₂ := b3e32 X1
             grind)
          | exact superpose b3e32 b3e12
          | exact resolve b3e12 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e46 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
          intro X1
          first
          | (have i₁ := b3e45 x X1
             have i₂ := b3e32 x
             grind)
          | exact superpose b3e32 b3e45
          | exact resolve b3e45 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e51 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ y = (k x y) := by
          first
          | (have i₁ := b3e16 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 x x
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e58 : y = (M.op x x) ∨ y = (k x y) := by grind
        clear b3e51
        have b3e63 : y = (k x y) := by
          first
          | (have r₁ := b3e58
             have r₂ := b3e23
             grind)
          | exact resolve b3e58 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e58
        have b3e79 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X0 X0
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e16 X0 X1
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e16
          | (have j0 := b3e16 X0 X1
             have j1 := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X1 X1
             have r₂ := b3e17 X1 X1
             grind)
          | (have r₁ := b3e16 X0 (M.op X0 X0)
             have r₂ := b3e17 X0 (M.op X0 X0)
             grind)
          | exact resolve b3e16 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e82 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e17 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e83 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e79 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e79
        have b3e85 : ∀ X0 X1 : G, (σ y) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e82 X0 X1
             have i₂ := b3e32 X0
             grind)
          | exact superpose b3e32 b3e82
          | (have j0 := b3e82 X0 X1
             grind)
          | (have r₁ := b3e82 X0 (σ y)
             have r₂ := b3e32 X0
             grind)
          | exact resolve b3e82 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e82
        have b3e87 : ∀ X0 X1 : G, (σ y) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e83 X0 X1
             have i₂ := b3e32 X0
             grind)
          | exact superpose b3e32 b3e83
          | (have j0 := b3e83 X0 X1
             grind)
          | exact resolve b3e83 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e83
        have b3e93 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e87 X0 X1
             have j1 := b3e85 X0 X1
             grind)
          | (have r₁ := b3e87 X0 X1
             have r₂ := b3e85 X0 X1
             grind)
          | (have r₁ := b3e87 X0 (σ y)
             have r₂ := b3e85 X0 (σ y)
             grind)
          | (have r₁ := b3e87 X0 (σ y)
             have r₂ := b3e85 X0 (k X0 (σ y))
             grind)
          | exact resolve b3e87 b3e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85 b3e87
        have b3e138 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e39
             have i₂ := b3e63
             grind)
          | exact superpose b3e63 b3e39
          | exact resolve b3e39 b3e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e63
        have b3e153 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e138
             grind)
          | exact superpose b3e138 b3e13
          | exact resolve b3e13 b3e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e154 : x = y := by
          first
          | (have i₁ := b3e153
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e153
          | exact resolve b3e153 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e153
        have b3e192 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X1 X1) X2) ∨ (M.op (M.op X1 X1) X2) = X2 ∨ (k (M.op X1 X1) X2) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e16 (M.op X1 X1) X2
             have i₂ := b3e30 X1 X0 (M.op X1 X1)
             grind)
          | (have i₁ := b3e16 X1 X1
             have i₂ := b3e30 X0 X1 X2
             grind)
          | exact superpose b3e30 b3e16
          | (have j0 := b3e16 (M.op X1 X1) X2
             grind)
          | (have r₁ := b3e16 X2 (M.op X0 X0)
             have r₂ := b3e30 X0 X2 X2
             grind)
          | (have r₁ := b3e16 (M.op X0 X0) (M.op X0 X0)
             have r₂ := b3e30 X0 (M.op X0 X0) (M.op X0 X0)
             grind)
          | exact resolve b3e16 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e199 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (k X1 (M.op X2 X2)) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e15 X1 (M.op X2 X2)
             have i₂ := b3e30 X2 X0 X1
             grind)
          | (have i₁ := b3e15 X1 X1
             have i₂ := b3e30 X0 X1 X2
             grind)
          | exact superpose b3e30 b3e15
          | (have j0 := b3e15 X1 (M.op X2 X2)
             grind)
          | (have r₁ := b3e15 (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X0 X0))
             have r₂ := b3e30 X0 (M.op X2 (M.op X0 X0)) X2
             grind)
          | (have r₁ := b3e15 X2 (M.op X1 X1)
             have r₂ := b3e30 X1 X1 X2
             grind)
          | exact resolve b3e15 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e202 : ∀ X1 X2 : G, (k X1 (M.op X2 X2)) = X1 := by
          intro X1 X2
          first
          | (have j0 := b3e199 x X1 X2
             grind)
          | (have r₁ := b3e199 x X1 X1
             have r₂ := b3e31 x X1
             grind)
          | (have r₁ := b3e199 X1 X1 x
             have r₂ := b3e31 x X1
             grind)
          | exact resolve b3e199 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31 b3e199
        have b3e204 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (σ y) X2) ∨ (M.op (M.op X1 X1) X2) = X2 ∨ (k (M.op X1 X1) X2) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e192 X0 X1 X2
             have i₂ := b3e32 X1
             grind)
          | exact superpose b3e32 b3e192
          | (have j0 := b3e192 X0 X1 X2
             grind)
          | exact resolve b3e192 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e192
        have b3e218 : ∀ X1 : G, (k X1 (σ y)) = X1 := by
          intro X1
          first
          | (have i₁ := b3e202 X1 x
             have i₂ := b3e32 x
             grind)
          | exact superpose b3e32 b3e202
          | exact resolve b3e202 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e202
        have b3e220 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (σ x) X2) ∨ (M.op (M.op X1 X1) X2) = X2 ∨ (k (M.op X1 X1) X2) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e204 X0 X1 X2
             have i₂ := b3e138
             grind)
          | exact superpose b3e138 b3e204
          | (have j0 := b3e204 X0 X1 X2
             grind)
          | exact resolve b3e204 b3e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e204
        have b3e231 : ∀ X1 : G, (k X1 (σ x)) = X1 := by
          intro X1
          first
          | (have i₁ := b3e218 X1
             have i₂ := b3e138
             grind)
          | exact superpose b3e138 b3e218
          | exact resolve b3e218 b3e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e218
        have b3e233 : ∀ X1 X2 : G, (σ y) ≠ (M.op (σ x) X2) ∨ (M.op (M.op X1 X1) X2) = X2 ∨ (k (M.op X1 X1) X2) = X2 := by
          intro X1 X2
          first
          | (have i₁ := b3e220 x X1 X2
             have i₂ := b3e32 x
             grind)
          | exact superpose b3e32 b3e220
          | (have j0 := b3e220 x X1 X2
             grind)
          | exact resolve b3e220 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e220
        have b3e239 : ∀ X1 X2 : G, (σ x) ≠ (M.op (σ x) X2) ∨ (M.op (M.op X1 X1) X2) = X2 ∨ (k (M.op X1 X1) X2) = X2 := by
          intro X1 X2
          first
          | (have i₁ := b3e233 X1 X2
             have i₂ := b3e138
             grind)
          | exact superpose b3e138 b3e233
          | (have j0 := b3e233 X1 X2
             grind)
          | exact resolve b3e233 b3e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e233
        have b3e242 : ∀ X1 X2 : G, (M.op (σ y) X2) = X2 ∨ (σ x) ≠ (M.op (σ x) X2) ∨ (k (M.op X1 X1) X2) = X2 := by
          intro X1 X2
          first
          | (have i₁ := b3e239 X1 X2
             have i₂ := b3e32 X1
             grind)
          | exact superpose b3e32 b3e239
          | (have j0 := b3e239 X1 X2
             grind)
          | exact resolve b3e239 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e239
        have b3e245 : ∀ X1 X2 : G, (M.op (σ x) X2) = X2 ∨ (σ x) ≠ (M.op (σ x) X2) ∨ (k (M.op X1 X1) X2) = X2 := by
          intro X1 X2
          first
          | (have i₁ := b3e242 X1 X2
             have i₂ := b3e138
             grind)
          | exact superpose b3e138 b3e242
          | (have j0 := b3e242 X1 X2
             grind)
          | exact resolve b3e242 b3e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e242
        have b3e248 : ∀ X2 : G, (k (σ y) X2) = X2 ∨ (M.op (σ x) X2) = X2 ∨ (σ x) ≠ (M.op (σ x) X2) := by
          intro X2
          first
          | (have i₁ := b3e245 x X2
             have i₂ := b3e32 x
             grind)
          | exact superpose b3e32 b3e245
          | (have j0 := b3e245 x X2
             grind)
          | exact resolve b3e245 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32 b3e245
        have b3e251 : ∀ X2 : G, (σ x) ≠ (M.op (σ x) X2) ∨ (M.op (σ x) X2) = X2 ∨ (k (σ x) X2) = X2 := by
          intro X2
          first
          | (have i₁ := b3e248 X2
             have i₂ := b3e138
             grind)
          | exact superpose b3e138 b3e248
          | (have j0 := b3e248 X2
             grind)
          | exact resolve b3e248 b3e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e248
        have b3e256 : x ≠ (σ x) := by
          first
          | (have i₁ := b3e42
             have i₂ := b3e154
             grind)
          | exact superpose b3e154 b3e42
          | exact resolve b3e42 b3e154
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42 b3e154
        have b3e550 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 x
             have i₂ := b3e231 (σ X0)
             grind)
          | exact superpose b3e231 b3e18
          | exact resolve b3e18 b3e231
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e231
        have b3e634 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e46 x
             have i₂ := b3e138
             grind)
          | exact superpose b3e138 b3e46
          | exact resolve b3e46 b3e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46 b3e138
        have b3e701 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b3e13 (k X0 x)
             have i₂ := b3e550 X0
             grind)
          | exact superpose b3e550 b3e13
          | exact resolve b3e13 b3e550
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e550
        have b3e702 : ∀ X0 : G, (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b3e701 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e701
          | exact resolve b3e701 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e701
        have b3e737 : ∀ X0 : G, x = (M.op X0 x) ∨ (M.op X0 x) = X0 ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b3e93 X0 x
             have i₂ := b3e702 X0
             grind)
          | exact superpose b3e702 b3e93
          | (have j0 := b3e93 X0 x
             grind)
          | exact resolve b3e93 b3e702
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e93
        have b3e767 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (σ x) X0 X1
             have i₂ := b3e634 (σ x)
             grind)
          | exact superpose b3e634 b3e12
          | exact resolve b3e12 b3e634
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e634
        have b3e3050 : (σ x) ≠ (σ x) ∨ x = (σ x) ∨ x = (k (σ x) x) ∨ x = (M.op (σ x) x) ∨ x = (σ x) := by
          first
          | (have i₁ := b3e251 x
             have i₂ := b3e737 (σ x)
             grind)
          | exact superpose b3e737 b3e251
          | (have j0 := b3e251 x
             have j1 := b3e737 (σ x)
             grind)
          | (have r₁ := b3e251 x
             have r₂ := b3e737 (σ x)
             grind)
          | exact resolve b3e251 b3e737
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e251 b3e737
        have b3e3056 : (σ x) ≠ (σ x) ∨ x = (σ x) ∨ x = (k (σ x) x) ∨ x = (M.op (σ x) x) := by grind
        clear b3e3050
        have b3e3057 : x = (σ x) ∨ x = (k (σ x) x) ∨ x = (M.op (σ x) x) := by grind
        clear b3e3056
        have b3e3067 : x = (k (σ x) x) ∨ x = (M.op (σ x) x) := by
          first
          | (have r₁ := b3e3057
             have r₂ := b3e256
             grind)
          | exact resolve b3e3057 b3e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3057
        have b3e3084 : x = (σ x) ∨ x = (M.op (σ x) x) := by
          first
          | (have i₁ := b3e3067
             have i₂ := b3e702 (σ x)
             grind)
          | exact superpose b3e702 b3e3067
          | exact resolve b3e3067 b3e702
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e702 b3e3067
        have b3e3095 : x = (M.op (σ x) x) := by
          first
          | (have r₁ := b3e3084
             have r₂ := b3e256
             grind)
          | exact resolve b3e3084 b3e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3084
        have b3e3177 : (σ x) = (M.op (σ x) x) := by
          first
          | (have i₁ := b3e767 (σ x) x
             have i₂ := b3e3095
             grind)
          | exact superpose b3e3095 b3e767
          | exact resolve b3e767 b3e3095
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e767
        have b3e3180 : x = (σ x) := by
          first
          | (have i₁ := b3e3177
             have i₂ := b3e3095
             grind)
          | exact superpose b3e3095 b3e3177
          | exact resolve b3e3177 b3e3095
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3095 b3e3177
        have b3e3187 : False := by grind
        exact b3e3187
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op x x) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
          have b4e29 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X4)) := by
            intro X0 X1 X3 X4
            first
            | (have i₁ := b4e13 x X3 X4
               have i₂ := b4e13 x X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e31 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 X3 X3
               have i₂ := b4e13 X3 X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X2 (M.op X2 x)
               have i₂ := b4e13 X0 X2 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 x x
               have i₂ := b4e13 X1 x x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e57 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e63 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b4e28
               have i₂ := b4e33 (σ x) X0
               grind)
            | (have i₁ := b4e28
               have i₂ := b4e33 X0 (σ x)
               grind)
            | exact superpose b4e33 b4e28
            | exact resolve b4e28 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28
          have b4e82 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = X2 ∨ (k X1 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 X1 X2
               have i₂ := b4e33 X1 X0
               grind)
            | (have i₁ := b4e17 X1 X2
               have i₂ := b4e33 X0 X1
               grind)
            | exact superpose b4e33 b4e17
            | (have j0 := b4e17 X1 X2
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e33 X1 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e33 X0 X0
               grind)
            | exact resolve b4e17 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e88 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X2) ∨ (M.op X1 X2) = (k X1 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 X1 (M.op X1 X2)
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e17
            | (have j0 := b4e17 X1 (M.op X1 X2)
               grind)
            | (have r₁ := b4e17 X1 (M.op X1 X2)
               have r₂ := b4e13 X1 X1 X2
               grind)
            | exact resolve b4e17 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e98 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X2) ∨ (M.op X1 X2) = (k X1 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e88 X0 X1 X2
               grind)
            | (have r₁ := b4e88 X0 X1 X2
               have r₂ := b4e33 X0 X1
               grind)
            | (have r₁ := b4e88 X1 X0 X2
               have r₂ := b4e33 X0 X1
               grind)
            | exact resolve b4e88 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e88
          have b4e111 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b4e154 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e63 X1
               have i₂ := b4e33 x X0
               grind)
            | (have i₁ := b4e63 X1
               have i₂ := b4e33 X0 x
               grind)
            | exact superpose b4e33 b4e63
            | exact resolve b4e63 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e63
          have b4e209 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (k X1 (M.op X2 X2)) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X1 (M.op X2 X2)
               have i₂ := b4e32 X2 X0 X1
               grind)
            | (have i₁ := b4e16 X1 X1
               have i₂ := b4e32 X0 X1 X2
               grind)
            | exact superpose b4e32 b4e16
            | (have j0 := b4e16 X1 (M.op X2 X2)
               grind)
            | (have r₁ := b4e16 (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X0 X0))
               have r₂ := b4e32 X0 (M.op X2 (M.op X0 X0)) X2
               grind)
            | (have r₁ := b4e16 X2 (M.op X1 X1)
               have r₂ := b4e32 X1 X1 X2
               grind)
            | exact resolve b4e16 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e212 : ∀ X1 X2 : G, (k X1 (M.op X2 X2)) = X1 := by
            intro X1 X2
            first
            | (have j0 := b4e209 x X1 X2
               grind)
            | (have r₁ := b4e209 x X1 X1
               have r₂ := b4e33 x X1
               grind)
            | (have r₁ := b4e209 X1 X1 x
               have r₂ := b4e33 x X1
               grind)
            | exact resolve b4e209 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e209
          have b4e224 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e57 X0 (M.op X1 X1)
               have i₂ := b4e212 (τ X0) X1
               grind)
            | exact superpose b4e212 b4e57
            | exact resolve b4e57 b4e212
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e212
          have b4e227 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e57 X0 X1
               grind)
            | exact superpose b4e57 b4e14
            | exact resolve b4e14 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57
          have b4e228 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e224 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e224
            | exact resolve b4e224 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e224
          have b4e255 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) ≠ (σ (M.op X3 X3)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e154 X3 x
               have i₂ := b4e32 X1 x X0
               grind)
            | (have i₁ := b4e154 X0 (M.op X0 X0)
               have i₂ := b4e32 X0 X1 (M.op X0 X0)
               grind)
            | exact superpose b4e32 b4e154
            | exact resolve b4e154 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e345 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X2 X2) ∨ (M.op X0 (M.op X0 X1)) = (M.op X2 X3) ∨ (M.op X2 X3) = (k X2 (M.op X2 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e17 X0 (M.op X0 X1)
               have i₂ := b4e29 X0 X1 X3 x
               grind)
            | (have i₁ := b4e17 X3 (M.op X3 x)
               have i₂ := b4e29 X0 X1 X3 x
               grind)
            | exact superpose b4e29 b4e17
            | (have j0 := b4e17 X2 (M.op X2 X3)
               grind)
            | exact resolve b4e17 b4e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29
          have b4e349 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 X3) ∨ (M.op X2 X3) = (k X2 (M.op X2 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b4e345 X0 X1 X2 X3
               grind)
            | (have r₁ := b4e345 X1 X2 X0 X3
               have r₂ := b4e13 X0 X1 X2
               grind)
            | exact resolve b4e345 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e345
          have b4e664 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op X3 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 X3 X3
               have i₂ := b4e98 X3 X0 X1
               grind)
            | (have i₁ := b4e13 X0 X1 X2
               have i₂ := b4e98 X0 X1 X2
               grind)
            | exact superpose b4e98 b4e13
            | (have j1 := b4e98 X2 X3 (M.op X0 X1)
               grind)
            | exact resolve b4e13 b4e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e98
          have b4e946 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e227 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e227
            | exact resolve b4e227 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e227
          have b4e1335 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e111 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2024 : ∀ X0 X1 X2 X3 X5 : G, (M.op X3 (M.op X0 (M.op X1 (M.op X1 X2)))) ≠ (σ (M.op X5 X5)) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b4e255 X3 x X5
               have i₂ := b4e31 X1 X2 x X0
               grind)
            | (have i₁ := b4e255 X0 (M.op X0 (M.op X0 X1)) X3
               have i₂ := b4e31 X0 X1 X2 (M.op X0 (M.op X0 X1))
               grind)
            | exact superpose b4e31 b4e255
            | exact resolve b4e255 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e255
          have b4e8521 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op X2 X2) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e82 X0 (σ X0) (σ X1)
               have i₂ := b4e111 X0 X1
               grind)
            | exact superpose b4e111 b4e82
            | (have j0 := b4e82 X0 (σ X0) (σ X1)
               have j1 := b4e111 X0 X1
               grind)
            | (have r₁ := b4e82 (σ X1) (σ X1) (σ X1)
               have r₂ := b4e111 X1 X1
               grind)
            | (have r₁ := b4e82 (σ X0) (σ X0) (σ X1)
               have r₂ := b4e111 X0 X1
               grind)
            | exact resolve b4e82 b4e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e82 b4e111
          have b4e8527 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op X2 X2) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e8521 X0 X1 X2
               have j1 := b4e1335 X0 X1
               grind)
            | (have r₁ := b4e8521 X0 X1 (σ (k X0 X1))
               have r₂ := b4e1335 (k X0 X1) (k X0 X1)
               grind)
            | (have r₁ := b4e8521 X0 X1 X2
               have r₂ := b4e1335 X0 X1
               grind)
            | exact resolve b4e8521 b4e1335
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1335 b4e8521
          have b4e8535 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op X2 X2) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e8527 X0 X1 X2
               have j1 := b4e17 (σ X0) (σ X1)
               grind)
            | (have r₁ := b4e8527 X0 X1 (σ (k X0 X1))
               have r₂ := b4e17 (σ (k X0 X1)) (σ (k X0 X1))
               grind)
            | (have r₁ := b4e8527 X0 X0 X2
               have r₂ := b4e17 (σ X0) (σ X0)
               grind)
            | (have r₁ := b4e8527 X0 X1 X2
               have r₂ := b4e17 (σ X0) (σ X1)
               grind)
            | exact resolve b4e8527 b4e17
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8527
          have b4e8538 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op X2 X2) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e8535 X0 X1 X2
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e8535
            | (have j0 := b4e8535 X0 X1 X2
               grind)
            | exact resolve b4e8535 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8535
          have b4e11435 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X4 X5) = (M.op X3 (M.op X0 (M.op X1 X2))) ∨ (M.op X4 X5) = (k X4 (M.op X4 X5)) ∨ (M.op X1 X2) = (k X1 (M.op X1 X2)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e349 X3 X3 X4 X5
               have i₂ := b4e664 X1 X2 X3 X0
               grind)
            | (have i₁ := b4e349 X3 (M.op X0 X1) X2 X3
               have i₂ := b4e664 X0 X1 X2 X3
               grind)
            | exact superpose b4e664 b4e349
            | (have j0 := b4e349 X0 X1 X4 X5
               have j1 := b4e664 X4 X5 X2 X3
               grind)
            | exact resolve b4e349 b4e664
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e349 b4e664
          have b4e392528 : ∀ X0 X1 X2 : G, (M.op X2 X2) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e8538 (τ X1) (τ X0) X2
               have i₂ := b4e946 X0 X1
               grind)
            | exact superpose b4e946 b4e8538
            | (have j0 := b4e8538 (τ X0) (τ X1) X2
               grind)
            | exact resolve b4e8538 b4e946
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e946 b4e8538
          have b4e392616 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ (M.op X2 X2) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e392528 X0 X1 X2
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e392528
            | (have j0 := b4e392528 X0 X1 X2
               grind)
            | exact resolve b4e392528 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e392528
          have b4e392619 : ∀ X0 X1 X2 : G, (k X0 X1) = (σ (τ X1)) ∨ (k X0 X1) ≠ (M.op X2 X2) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e392616 X0 X1 X2
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e392616
            | (have j0 := b4e392616 X0 X1 X2
               grind)
            | exact resolve b4e392616 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e392616
          have b4e392621 : ∀ X0 X1 X2 : G, (k X0 X1) = X1 ∨ (k X0 X1) ≠ (M.op X2 X2) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e392619 X0 X1 X2
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e392619
            | (have j0 := b4e392619 X0 X1 X2
               grind)
            | exact resolve b4e392619 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e392619
          have b4e392622 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ (M.op X2 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e392621 X0 X0 X2
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e392621
            | (have j0 := b4e392621 X0 X1 X2
               grind)
            | exact resolve b4e392621 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e392621
          have b4e392623 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ (M.op X2 X2) ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e392622 X0 X1 X2
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e392622
            | (have j0 := b4e392622 X0 X1 X2
               grind)
            | exact resolve b4e392622 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e392622
          have b4e392633 : ∀ X0 X1 X2 : G, (M.op X2 X2) ≠ X0 ∨ (σ (M.op X1 X1)) = X0 ∨ (σ (M.op X1 X1)) = (M.op X0 (σ (M.op X1 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e392623 X0 (σ (M.op X1 X1)) X2
               have i₂ := b4e228 X0 X1
               grind)
            | exact superpose b4e228 b4e392623
            | (have j0 := b4e392623 X0 (σ (M.op X1 X1)) X2
               grind)
            | (have r₁ := b4e392623 (M.op X2 X2) (σ (M.op X1 X1)) X2
               have r₂ := b4e228 (M.op X2 X2) X1
               grind)
            | exact resolve b4e392623 b4e228
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e392623
          have b4e711807 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X2 (M.op X3 (M.op X0 X1))) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b4e11435 X3 X0 X1 X2 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11435
          have b4e711808 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X3 (M.op X0 X1))) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b4e711807 X0 X1 X2 X3
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e711807
          have b4e854222 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (M.op X1 X1) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have j0 := b4e392633 (M.op X1 X1) X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e392633
          have b4e854223 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 X1) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have j0 := b4e854222 X0 X1
               grind)
            | (have r₁ := b4e854222 X0 X1
               have r₂ := b4e154 X0 X1
               grind)
            | exact resolve b4e854222 b4e154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e854222
          have b4e854743 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X4 X4)) ≠ (M.op X1 (M.op X2 (M.op (M.op X3 X3) (σ (M.op X0 X0))))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e2024 X2 (M.op X3 X3) (σ (M.op X0 X0)) X1 X4
               have i₂ := b4e854223 X0 X3
               grind)
            | exact superpose b4e854223 b4e2024
            | exact resolve b4e2024 b4e854223
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2024
          have b4e855308 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X0)) = (M.op X2 (M.op X3 (σ (M.op X0 X0)))) ∨ (σ (M.op X0 X0)) = (k (M.op X1 X1) (σ (M.op X0 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e711808 (M.op X1 X1) (σ (M.op X0 X0)) X2 X3
               have i₂ := b4e854223 X0 X1
               grind)
            | exact superpose b4e854223 b4e711808
            | exact resolve b4e711808 b4e854223
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e711808
          have b4e855336 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op X2 (M.op X3 (σ (M.op X0 X0)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e855308 X0 X1 X2 X3
               have i₂ := b4e228 (M.op X1 X1) X0
               grind)
            | exact superpose b4e228 b4e855308
            | (have j0 := b4e855308 X0 X1 X2 X3
               grind)
            | exact resolve b4e855308 b4e228
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e228 b4e855308
          have b4e855843 : ∀ X0 X1 X2 X4 : G, (σ (M.op X4 X4)) ≠ (M.op X1 (M.op X2 (σ (M.op X0 X0)))) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b4e854743 X0 X1 X2 x X4
               have i₂ := b4e854223 X0 x
               grind)
            | exact superpose b4e854223 b4e854743
            | exact resolve b4e854743 b4e854223
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e854223 b4e854743
          have b4e855937 : ∀ X0 X2 X3 : G, (σ (M.op X0 X0)) = (M.op X2 (M.op X3 (σ (M.op X0 X0)))) := by
            intro X0 X2 X3
            first
            | (have j0 := b4e855336 X0 x X2 X3
               grind)
            | (have r₁ := b4e855336 X0 x X2 X3
               have r₂ := b4e154 X0 x
               grind)
            | (have r₁ := b4e855336 X0 x (M.op X3 (σ (M.op X0 X0))) X3
               have r₂ := b4e154 X0 (M.op X3 (σ (M.op X0 X0)))
               grind)
            | exact resolve b4e855336 b4e154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e154 b4e855336
          have b4e856181 : False := by grind
          exact b4e856181
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x y) := by grind
          have b5e22 : (M.op x y) = (M.op x x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : y ≠ (M.op x x) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e109 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ y = (k x y) := by
            first
            | (have i₁ := b5e17 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 x x
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e121 : y = (M.op x x) ∨ y = (k x y) := by grind
          clear b5e109
          have b5e128 : y = (k x y) := by
            first
            | (have r₁ := b5e121
               have r₂ := b5e25
               grind)
            | exact resolve b5e121 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e121
          have b5e140 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X2 X3)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X2 X3
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e13 X1 X1 X2
               have i₂ := b5e18 X1 X1
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X0 X1
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e812 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e24
               have i₂ := b5e140 (σ x) (σ y) X0 X1
               grind)
            | exact superpose b5e140 b5e24
            | (have j1 := b5e140 (σ x) (σ y) x x
               grind)
            | exact resolve b5e24 b5e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e140
          have b5e917 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            intro X0 X1
            first
            | (have j0 := b5e812 X0 X1
               grind)
            | (have r₁ := b5e812 X0 X1
               have r₂ := b5e23
               grind)
            | exact resolve b5e812 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e812
          have b5e919 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e917 x x
               have r₂ := b5e13 (σ x) x x
               grind)
            | exact resolve b5e917 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e917
          have b5e921 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e919
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e919
            | exact resolve b5e919 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e919
          have b5e923 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e921
               have i₂ := b5e128
               grind)
            | exact superpose b5e128 b5e921
            | exact resolve b5e921 b5e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e128 b5e921
          have b5e924 : False := by grind
          exact b5e924
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X1 X2 (M.op X2 x)
             have i₂ := b6e12 X0 X2 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e28 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 x x
             have i₂ := b6e12 X1 x x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e29 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
          intro X0
          first
          | (have i₁ := b6e25 X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e25
          | exact resolve b6e25 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e39 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 X1
             have i₂ := b6e29 X1
             grind)
          | exact superpose b6e29 b6e12
          | exact resolve b6e12 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e40 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
          intro X1
          first
          | (have i₁ := b6e39 x X1
             have i₂ := b6e29 x
             grind)
          | exact superpose b6e29 b6e39
          | exact resolve b6e39 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e63 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (σ y) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X0 X1
             have i₂ := b6e29 X0
             grind)
          | exact superpose b6e29 b6e16
          | (have j0 := b6e16 X0 X1
             grind)
          | exact resolve b6e16 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e69 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X2) ∨ (M.op X1 X2) = (k X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e16 X1 (M.op X1 X2)
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e16
          | (have j0 := b6e16 X1 (M.op X1 X2)
             grind)
          | (have r₁ := b6e16 X1 (M.op X1 X2)
             have r₂ := b6e12 X1 X1 X2
             grind)
          | exact resolve b6e16 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e76 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X2) ∨ (M.op X1 X2) = (k X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e69 X0 X1 X2
             grind)
          | (have r₁ := b6e69 X0 X1 X2
             have r₂ := b6e28 X0 X1
             grind)
          | (have r₁ := b6e69 X1 X0 X2
             have r₂ := b6e28 X0 X1
             grind)
          | exact resolve b6e69 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e84 : ∀ X1 X2 : G, (M.op X1 X2) = (k X1 (M.op X1 X2)) ∨ (M.op X1 X2) = (σ y) := by
          intro X1 X2
          first
          | (have i₁ := b6e76 x X1 X2
             have i₂ := b6e29 x
             grind)
          | exact superpose b6e29 b6e76
          | (have j0 := b6e76 x X1 X2
             grind)
          | exact resolve b6e76 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e76
        have b6e102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X0 X0
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e16 X0 X1
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e16
          | (have j0 := b6e16 X0 X1
             have j1 := b6e17 X0 X1
             grind)
          | (have r₁ := b6e16 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e16 X1 X1
             have r₂ := b6e17 X1 X1
             grind)
          | (have r₁ := b6e16 X0 (M.op X0 X0)
             have r₂ := b6e17 X0 (M.op X0 X0)
             grind)
          | exact resolve b6e16 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e17 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e106 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e102 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e102
        have b6e108 : ∀ X0 X1 : G, (σ y) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e105 X0 X1
             have i₂ := b6e29 X0
             grind)
          | exact superpose b6e29 b6e105
          | (have j0 := b6e105 X0 X1
             grind)
          | (have r₁ := b6e105 X0 (σ y)
             have r₂ := b6e29 X0
             grind)
          | exact resolve b6e105 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e105
        have b6e110 : ∀ X0 X1 : G, (σ y) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e106 X0 X1
             have i₂ := b6e29 X0
             grind)
          | exact superpose b6e29 b6e106
          | (have j0 := b6e106 X0 X1
             grind)
          | exact resolve b6e106 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e106
        have b6e120 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e110 X0 X1
             have j1 := b6e108 X0 X1
             grind)
          | (have r₁ := b6e110 X0 X1
             have r₂ := b6e108 X0 X1
             grind)
          | (have r₁ := b6e110 X0 (σ y)
             have r₂ := b6e108 X0 (σ y)
             grind)
          | (have r₁ := b6e110 X0 (σ y)
             have r₂ := b6e108 X0 (k X0 (σ y))
             grind)
          | exact resolve b6e110 b6e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e108 b6e110
        have b6e171 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (k X1 (M.op X2 X2)) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 X1 (M.op X2 X2)
             have i₂ := b6e27 X2 X0 X1
             grind)
          | (have i₁ := b6e15 X1 X1
             have i₂ := b6e27 X0 X1 X2
             grind)
          | exact superpose b6e27 b6e15
          | (have j0 := b6e15 X1 (M.op X2 X2)
             grind)
          | (have r₁ := b6e15 (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X0 X0))
             have r₂ := b6e27 X0 (M.op X2 (M.op X0 X0)) X2
             grind)
          | (have r₁ := b6e15 X2 (M.op X1 X1)
             have r₂ := b6e27 X1 X1 X2
             grind)
          | exact resolve b6e15 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e174 : ∀ X1 X2 : G, (k X1 (M.op X2 X2)) = X1 := by
          intro X1 X2
          first
          | (have j0 := b6e171 x X1 X2
             grind)
          | (have r₁ := b6e171 x X1 X1
             have r₂ := b6e28 x X1
             grind)
          | (have r₁ := b6e171 X1 X1 x
             have r₂ := b6e28 x X1
             grind)
          | exact resolve b6e171 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28 b6e171
        have b6e190 : ∀ X1 : G, (k X1 (σ y)) = X1 := by
          intro X1
          first
          | (have i₁ := b6e174 X1 x
             have i₂ := b6e29 x
             grind)
          | exact superpose b6e29 b6e174
          | exact resolve b6e174 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29 b6e174
        have b6e518 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 y
             have i₂ := b6e190 (σ X0)
             grind)
          | exact superpose b6e190 b6e18
          | exact resolve b6e18 b6e190
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e190
        have b6e631 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b6e13 (k X0 y)
             have i₂ := b6e518 X0
             grind)
          | exact superpose b6e518 b6e13
          | exact resolve b6e13 b6e518
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e518
        have b6e632 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e631 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e631
          | exact resolve b6e631 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e631
        have b6e647 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op X0 y) = X0 ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b6e120 X0 y
             have i₂ := b6e632 X0
             grind)
          | exact superpose b6e632 b6e120
          | (have j0 := b6e120 X0 y
             grind)
          | exact resolve b6e120 b6e632
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e120
        have b6e2190 : ∀ X0 : G, (σ y) ≠ X0 ∨ y = X0 ∨ y = (k X0 y) ∨ y = (M.op X0 y) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b6e63 X0 y
             have i₂ := b6e647 X0
             grind)
          | exact superpose b6e647 b6e63
          | (have j0 := b6e63 X0 y
             have j1 := b6e647 X0
             grind)
          | (have r₁ := b6e63 (σ y) y
             have r₂ := b6e647 (σ y)
             grind)
          | exact resolve b6e63 b6e647
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63 b6e647
        have b6e2205 : ∀ X0 : G, (σ y) ≠ X0 ∨ y = X0 ∨ y = (k X0 y) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b6e2190 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2190
        have b6e2217 : ∀ X0 : G, y = X0 ∨ (σ y) ≠ X0 ∨ y = X0 ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b6e2205 X0
             have i₂ := b6e632 X0
             grind)
          | exact superpose b6e632 b6e2205
          | (have j0 := b6e2205 X0
             grind)
          | (have r₁ := b6e2205 (k (σ y) y)
             have r₂ := b6e632 (σ y)
             grind)
          | exact resolve b6e2205 b6e632
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2205
        have b6e2218 : ∀ X0 : G, (σ y) ≠ X0 ∨ y = X0 ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b6e2217 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2217
        have b6e2298 : y = (M.op (σ y) y) ∨ y = (σ y) := by
          first
          | (have j0 := b6e2218 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2218
        have b6e2382 : y = (k (σ y) y) ∨ y = (σ y) ∨ y = (σ y) := by
          first
          | (have i₁ := b6e84 (σ y) y
             have i₂ := b6e2298
             grind)
          | exact superpose b6e2298 b6e84
          | exact resolve b6e84 b6e2298
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84 b6e2298
        have b6e2383 : y = (k (σ y) y) ∨ y = (σ y) := by grind
        clear b6e2382
        have b6e2386 : y = (σ y) ∨ y = (σ y) := by
          first
          | (have i₁ := b6e2383
             have i₂ := b6e632 (σ y)
             grind)
          | exact superpose b6e632 b6e2383
          | exact resolve b6e2383 b6e632
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e632 b6e2383
        have b6e2387 : y = (σ y) := by grind
        clear b6e2386
        have b6e2477 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b6e40 x
             have i₂ := b6e2387
             grind)
          | exact superpose b6e2387 b6e40
          | exact resolve b6e40 b6e2387
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e2387
        have b6e2935 : y ≠ y := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e2477 x
             grind)
          | exact superpose b6e2477 b6e20
          | (have r₁ := b6e20
             have r₂ := b6e2477 x
             grind)
          | exact resolve b6e20 b6e2477
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2477
        have b6e2936 : False := by grind
        exact b6e2936
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x y) := by grind
          have b7e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e81 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) (σ x)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e83 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e81
          have b7e88 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e83
               have r₂ := b7e25
               grind)
            | exact resolve b7e83 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e83
          have b7e93 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e88
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e88
            | exact resolve b7e88 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e128 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e93
               grind)
            | exact superpose b7e93 b7e14
            | exact resolve b7e14 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93
          have b7e129 : y = (k x y) := by
            first
            | (have i₁ := b7e128
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e128
            | exact resolve b7e128 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e128
          have b7e190 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e129
               grind)
            | exact superpose b7e129 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e129
          have b7e191 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b7e190
          have b7e193 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b7e191
               have r₂ := b7e21
               grind)
            | exact resolve b7e191 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e191
          have b7e195 : False := by grind
          exact b7e195
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x y) := by grind
          have b8e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e136 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X2 X3)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
          have b8e737 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b8e24
               have i₂ := b8e136 (σ x) (σ y) X0 X1
               grind)
            | exact superpose b8e136 b8e24
            | (have j1 := b8e136 (σ x) (σ y) x x
               grind)
            | exact resolve b8e24 b8e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e136
          have b8e831 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            intro X0 X1
            first
            | (have j0 := b8e737 X0 X1
               grind)
            | (have r₁ := b8e737 X0 X1
               have r₂ := b8e23
               grind)
            | exact resolve b8e737 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e737
          have b8e833 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e831 x x
               have r₂ := b8e13 (σ x) x x
               grind)
            | exact resolve b8e831 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e831
          have b8e834 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e833
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e833
            | exact resolve b8e833 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e833
          have b8e838 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e834
               grind)
            | exact superpose b8e834 b8e20
            | exact resolve b8e20 b8e834
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e834
          have b8e1298 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e838
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e838
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e838 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e838
          have b8e1299 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
          clear b8e1298
          have b8e1303 : y = (M.op x y) := by
            first
            | (have r₁ := b8e1299
               have r₂ := b8e22
               grind)
            | exact resolve b8e1299 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1299
          have b8e1307 : False := by grind
          exact b8e1307
