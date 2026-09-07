import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4301`: `x ◇ (x ◇ y) = z ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation4301 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4301 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4301.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e28 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e11 y y X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e29 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ y) (σ y) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 : G, (M.op y y) = (M.op y (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e11 y X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e34 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e34
        | exact resolve b0e34 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e42 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e29 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e29
        | exact resolve b0e29 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e43 : ∀ X0 : G, y = (M.op X0 (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e28 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e28
        | exact resolve b0e28 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e52 : ∀ X0 X1 : G, (M.op y (M.op y X0)) = (M.op (M.op y X1) y) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 y X0 (M.op y X1)
           have i₂ := b0e41 X1
           grind)
        | exact superpose b0e41 b0e11
        | exact resolve b0e11 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X1 : G, y = (M.op (M.op y X1) y) := by
        intro X1
        first
        | (have i₁ := b0e52 x X1
           have i₂ := b0e41 x
           grind)
        | exact superpose b0e41 b0e52
        | exact resolve b0e52 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e52
      have b0e57 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 X0 y
           grind)
        | (have r₁ := b0e14 X0 y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e58 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 X0 (σ y)
           grind)
        | (have r₁ := b0e14 X0 (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e59 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
        intro X0
        first
        | (have j0 := b0e58 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58
      have b0e60 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
        intro X0
        first
        | (have j0 := b0e57 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57
      have b0e71 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op y X0) y) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (M.op y X0)
           have i₂ := b0e43 X0
           grind)
        | exact superpose b0e43 b0e11
        | exact resolve b0e11 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e72 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 (M.op y X0) X1
           have i₂ := b0e43 X0
           grind)
        | exact superpose b0e43 b0e11
        | exact resolve b0e11 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e73 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y := by
        intro X0 X1
        first
        | (have i₁ := b0e71 X0 X1
           have i₂ := b0e55 X0
           grind)
        | exact superpose b0e55 b0e71
        | exact resolve b0e71 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55 b0e71
      have b0e105 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X0 (k X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X0 X1
           have i₂ := b0e60 X0
           grind)
        | exact superpose b0e60 b0e11
        | exact resolve b0e11 b0e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e110 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (k X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e105 X0 x
           have i₂ := b0e72 X0 x
           grind)
        | exact superpose b0e72 b0e105
        | exact resolve b0e105 b0e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72 b0e105
      have b0e148 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (k X0 (σ y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 X0
           have i₂ := b0e59 X0
           grind)
        | exact superpose b0e59 b0e11
        | exact resolve b0e11 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e151 : ∀ X0 : G, (k X0 y) = (k X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e60 X0
           have i₂ := b0e59 X0
           grind)
        | exact superpose b0e59 b0e60
        | exact resolve b0e60 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59 b0e60
      have b0e163 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (k X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e148 X0 X1
           have i₂ := b0e151 X0
           grind)
        | exact superpose b0e151 b0e148
        | exact resolve b0e148 b0e151
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e148 b0e151
      have b0e169 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e163 X0 X1
           have i₂ := b0e110 X0
           grind)
        | exact superpose b0e110 b0e163
        | exact resolve b0e163 b0e110
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e110 b0e163
      have b0e172 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e169 X0 x
           have i₂ := b0e73 X0 x
           grind)
        | exact superpose b0e73 b0e169
        | exact resolve b0e169 b0e73
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e73 b0e169
      have b0e191 : (σ y) = (M.op y y) := by
        first
        | (have i₁ := b0e42 y
           have i₂ := b0e172 (σ y)
           grind)
        | exact superpose b0e172 b0e42
        | exact resolve b0e42 b0e172
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e204 : y = (σ y) := by
        first
        | (have i₁ := b0e191
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e191
        | exact resolve b0e191 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e191
      have b0e217 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e204
           grind)
        | exact superpose b0e204 b0e18
        | exact resolve b0e18 b0e204
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e222 : y ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e217
           have i₂ := b0e172 (σ x)
           grind)
        | exact superpose b0e172 b0e217
        | exact resolve b0e217 b0e172
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e217
      have b0e223 : y ≠ (σ y) := by
        first
        | (have i₁ := b0e222
           have i₂ := b0e172 x
           grind)
        | exact superpose b0e172 b0e222
        | exact resolve b0e222 b0e172
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e172 b0e222
      have b0e224 : False := by grind
      exact b0e224
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e53 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b1e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e53 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b1e89 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) y) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e86 X0 X1
             have i₂ := b1e55 (σ X1)
             grind)
          | exact superpose b1e55 b1e86
          | (have j0 := b1e86 X0 X1
             grind)
          | exact resolve b1e86 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e86
        have b1e95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) y) ∨ (σ X1) = (k (σ X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b1e89 X0 X1
             have i₂ := b1e55 (σ X0)
             grind)
          | exact superpose b1e55 b1e89
          | (have j0 := b1e89 X0 X1
             grind)
          | exact resolve b1e89 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e89
        have b1e101 : (σ y) ≠ (k (σ y) y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e55 (σ y)
             grind)
          | exact superpose b1e55 b1e21
          | exact resolve b1e21 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e4921 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e95 y y
             grind)
          | exact superpose b1e95 b1e21
          | (have j1 := b1e95 y y
             grind)
          | exact resolve b1e21 b1e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e95
        have b1e4992 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) := by grind
        clear b1e4921
        have b1e5039 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b1e4992
             have r₂ := b1e101
             grind)
          | exact resolve b1e4992 b1e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e101 b1e4992
        have b1e5061 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e5039
             have i₂ := b1e55 y
             grind)
          | exact superpose b1e55 b1e5039
          | exact resolve b1e5039 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e5039
        have b1e5065 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e5061
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e5061
          | exact resolve b1e5061 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5061
        have b1e5066 : False := by grind
        exact b1e5066
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e51 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b2e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b2e51 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51
        have b2e81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b2e84 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) y) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e81 X0 X1
             have i₂ := b2e52 (σ X1)
             grind)
          | exact superpose b2e52 b2e81
          | (have j0 := b2e81 X0 X1
             grind)
          | exact resolve b2e81 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e81
        have b2e90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) y) ∨ (σ X1) = (k (σ X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b2e84 X0 X1
             have i₂ := b2e52 (σ X0)
             grind)
          | exact superpose b2e52 b2e84
          | (have j0 := b2e84 X0 X1
             grind)
          | exact resolve b2e84 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84
        have b2e95 : (σ y) ≠ (k (σ y) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e52 (σ y)
             grind)
          | exact superpose b2e52 b2e21
          | exact resolve b2e21 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e4401 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e90 y y
             grind)
          | exact superpose b2e90 b2e21
          | (have j1 := b2e90 y y
             grind)
          | exact resolve b2e21 b2e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90
        have b2e4467 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) := by grind
        clear b2e4401
        have b2e4511 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b2e4467
             have r₂ := b2e95
             grind)
          | exact resolve b2e4467 b2e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e95 b2e4467
        have b2e4533 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e4511
             have i₂ := b2e52 y
             grind)
          | exact superpose b2e52 b2e4511
          | exact resolve b2e4511 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e4511
        have b2e4538 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e4533
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e4533
          | exact resolve b2e4533 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4533
        have b2e4539 : False := by grind
        exact b2e4539
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 x x X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e27 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) (σ y) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e29 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X2 (M.op X0 X2) X3
             have i₂ := b3e12 X0 X1 X2
             grind)
          | (have i₁ := b3e12 X0 (M.op X0 X1) X2
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e12 X1 x X3
             have i₂ := b3e12 X1 x X0
             grind)
          | (have i₁ := b3e12 X0 X0 x
             have i₂ := b3e12 X0 X1 X0
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) X0 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b3e33 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e33
          | exact resolve b3e33 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e39 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b3e27 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e27
          | exact resolve b3e27 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e40 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x X1) (M.op X0 (M.op x X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e26 (M.op x X1)
             have i₂ := b3e12 x X1 X0
             grind)
          | (have i₁ := b3e26 (M.op X0 x)
             have i₂ := b3e12 X0 X1 x
             grind)
          | exact superpose b3e12 b3e26
          | exact resolve b3e26 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e48 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X0 (M.op x y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (M.op x X0) X1
             have i₂ := b3e26 X0
             grind)
          | exact superpose b3e26 b3e12
          | exact resolve b3e12 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e50 : ∀ X1 : G, (M.op x y) = (M.op (M.op x X1) (M.op x y)) := by
          intro X1
          first
          | (have i₁ := b3e40 x X1
             have i₂ := b3e26 x
             grind)
          | exact superpose b3e26 b3e40
          | exact resolve b3e40 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e52 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b3e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e52 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e125 : (σ y) = (M.op (M.op x (σ y)) (M.op x y)) := by
          first
          | (have i₁ := b3e39 (M.op x (σ y))
             have i₂ := b3e26 (σ y)
             grind)
          | exact superpose b3e26 b3e39
          | exact resolve b3e39 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e133 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (M.op (σ y) X0) X1
             have i₂ := b3e39 X0
             grind)
          | exact superpose b3e39 b3e12
          | exact resolve b3e12 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e136 : (M.op x y) = (σ y) := by
          first
          | (have i₁ := b3e125
             have i₂ := b3e50 (σ y)
             grind)
          | exact superpose b3e50 b3e125
          | exact resolve b3e125 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50 b3e125
        have b3e289 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X1 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e38 (M.op X1 (σ y))
             have i₂ := b3e30 (σ y) X1 X0
             grind)
          | (have i₁ := b3e38 (M.op X1 (σ y))
             have i₂ := b3e30 X0 X1 (σ y)
             grind)
          | exact superpose b3e30 b3e38
          | exact resolve b3e38 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30 b3e38
        have b3e301 : ∀ X1 : G, (σ y) = (M.op (σ y) (M.op X1 (σ y))) := by
          intro X1
          first
          | (have i₁ := b3e289 x X1
             have i₂ := b3e133 X1 x
             grind)
          | exact superpose b3e133 b3e289
          | exact resolve b3e289 b3e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e133 b3e289
        have b3e343 : ∀ X1 : G, (σ y) = (M.op X1 (M.op x y)) := by
          intro X1
          first
          | (have i₁ := b3e301 X1
             have i₂ := b3e48 X1 (σ y)
             grind)
          | exact superpose b3e48 b3e301
          | exact resolve b3e301 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e301
        have b3e366 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
          intro X1
          first
          | (have i₁ := b3e343 X1
             have i₂ := b3e136
             grind)
          | exact superpose b3e136 b3e343
          | exact resolve b3e343 b3e136
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e136 b3e343
        have b3e390 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 (σ y)
             have i₂ := b3e366 X0
             grind)
          | exact superpose b3e366 b3e12
          | exact resolve b3e12 b3e366
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e366
        have b3e402 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ y) := by
          intro X0 X1
          first
          | (have i₁ := b3e390 X0 X1
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e390
          | exact resolve b3e390 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e390
        have b3e1022 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X0)) = (k (M.op X1 (M.op X1 X2)) (σ y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e53 (M.op X1 (M.op X1 X2))
             have i₂ := b3e29 X1 X2 (M.op X1 (M.op X1 X2)) X0
             grind)
          | exact superpose b3e29 b3e53
          | exact resolve b3e53 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e53
        have b3e1055 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = (k (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e1022 X0 X0 x
             have i₂ := b3e402 X0 x
             grind)
          | exact superpose b3e402 b3e1022
          | exact resolve b3e1022 b3e402
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e402 b3e1022
        have b3e1158 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = (σ (k y y)) := by
          intro X0
          first
          | (have i₁ := b3e1055 X0
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e1055
          | exact resolve b3e1055 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1055
        have b3e1233 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e1158 x
             have i₂ := b3e39 x
             grind)
          | exact superpose b3e39 b3e1158
          | exact resolve b3e1158 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e1158
        have b3e1276 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e1233
             grind)
          | exact superpose b3e1233 b3e13
          | exact resolve b3e13 b3e1233
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1233
        have b3e1278 : y = (k y y) := by
          first
          | (have i₁ := b3e1276
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e1276
          | exact resolve b3e1276 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1276
        have b3e1904 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e1278
             grind)
          | exact superpose b3e1278 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e1278
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1278
        have b3e1905 : y = (M.op y y) := by grind
        clear b3e1904
        have b3e1907 : False := by grind
        exact b3e1907
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e32 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 x x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e13 X1 x X3
               have i₂ := b4e13 X1 x X0
               grind)
            | (have i₁ := b4e13 X0 X0 x
               have i₂ := b4e13 X0 X1 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X1 x
               have i₂ := b4e13 X0 X2 x
               grind)
            | (have i₁ := b4e13 X1 X1 X1
               have i₂ := b4e13 X1 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x X1) (M.op X0 (M.op x X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 (M.op x X1)
               have i₂ := b4e13 x X1 X0
               grind)
            | (have i₁ := b4e32 (M.op X0 x)
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e32
            | exact resolve b4e32 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e54 : ∀ X1 : G, (M.op x y) = (M.op (M.op x X1) (M.op x y)) := by
            intro X1
            first
            | (have i₁ := b4e44 x X1
               have i₂ := b4e32 x
               grind)
            | exact superpose b4e32 b4e44
            | exact resolve b4e44 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e83 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X2 X2) = (k X2 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
          have b4e148 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op x X1) (M.op x y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e36 X0 X1 (M.op x X1)
               have i₂ := b4e32 X1
               grind)
            | exact superpose b4e32 b4e36
            | exact resolve b4e36 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e178 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e148 X0 X1
               have i₂ := b4e54 X1
               grind)
            | exact superpose b4e54 b4e148
            | exact resolve b4e148 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e148
          have b4e190 : (M.op x y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e178 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e178
            | exact resolve b4e178 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e199 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 x
               have i₂ := b4e178 x X0
               grind)
            | exact superpose b4e178 b4e13
            | exact resolve b4e13 b4e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e178
          have b4e242 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op x y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e43 X0 X1 (M.op x X0)
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e43
            | exact resolve b4e43 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32 b4e43
          have b4e296 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b4e242 X0 x
               have i₂ := b4e199 X0 x
               grind)
            | exact superpose b4e199 b4e242
            | exact resolve b4e242 b4e199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e242
          have b4e418 : (M.op x y) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e190
               grind)
            | exact superpose b4e190 b4e20
            | exact resolve b4e20 b4e190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e190
          have b4e7878 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e83 X1 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83
          have b4e7879 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e7878 X0 X1
               have j1 := b4e16 X0 X1
               grind)
            | (have r₁ := b4e7878 X0 X1
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e7878 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7878
          have b4e11296 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e7879 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7879
          have b4e11297 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e11296 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11296
          have b4e11326 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e11297 (σ X0)
               grind)
            | exact superpose b4e11297 b4e19
            | exact resolve b4e19 b4e11297
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e11335 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e11326 X0
               have i₂ := b4e11297 X0
               grind)
            | exact superpose b4e11297 b4e11326
            | exact resolve b4e11326 b4e11297
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11297 b4e11326
          have b4e12095 : ∀ X0 : G, (M.op x y) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e199 (σ X0) (σ X0)
               have i₂ := b4e11335 X0
               grind)
            | exact superpose b4e11335 b4e199
            | exact resolve b4e199 b4e11335
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e199
          have b4e20597 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e12095 (M.op x y)
               have i₂ := b4e54 y
               grind)
            | exact superpose b4e54 b4e12095
            | exact resolve b4e12095 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54 b4e12095
          have b4e20712 : (M.op x y) = (σ (M.op (M.op x y) (M.op x y))) := by
            first
            | (have i₁ := b4e20597
               have i₂ := b4e11335 (M.op x y)
               grind)
            | exact superpose b4e11335 b4e20597
            | exact resolve b4e20597 b4e11335
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11335 b4e20597
          have b4e20772 : (M.op x y) = (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20712
               have i₂ := b4e296 (M.op x y)
               grind)
            | exact superpose b4e296 b4e20712
            | exact resolve b4e20712 b4e296
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e296 b4e20712
          have b4e20797 : False := by grind
          exact b4e20797
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
            intro X0 X1 X2
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b5e32 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 x x X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op X0 X2) X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | (have i₁ := b5e13 X0 (M.op X0 X1) X2
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e13 X1 x X3
               have i₂ := b5e13 X1 x X0
               grind)
            | (have i₁ := b5e13 X0 X0 x
               have i₂ := b5e13 X0 X1 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x X1) (M.op X0 (M.op x X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e32 (M.op x X1)
               have i₂ := b5e13 x X1 X0
               grind)
            | (have i₁ := b5e32 (M.op X0 x)
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e32
            | exact resolve b5e32 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e52 : ∀ X1 : G, (M.op x y) = (M.op (M.op x X1) (M.op x y)) := by
            intro X1
            first
            | (have i₁ := b5e42 x X1
               have i₂ := b5e32 x
               grind)
            | exact superpose b5e32 b5e42
            | exact resolve b5e42 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e80 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
          have b5e94 : y = (M.op y y) ∨ y = (k x y) := by grind
          have b5e107 : y = (k x y) := by
            first
            | (have r₁ := b5e94
               have r₂ := b5e21
               grind)
            | exact resolve b5e94 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e94
          have b5e141 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op x X1) (M.op x y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e35 X0 X1 (M.op x X1)
               have i₂ := b5e32 X1
               grind)
            | exact superpose b5e32 b5e35
            | exact resolve b5e35 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e35
          have b5e167 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e141 X0 X1
               have i₂ := b5e52 X1
               grind)
            | exact superpose b5e52 b5e141
            | exact resolve b5e141 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52 b5e141
          have b5e188 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 x
               have i₂ := b5e167 x X0
               grind)
            | exact superpose b5e167 b5e13
            | exact resolve b5e13 b5e167
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2561 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e80 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e80
          have b5e2562 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e2561
               have r₂ := b5e23
               grind)
            | exact resolve b5e2561 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2561
          have b5e2563 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e2562
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e2562
            | exact resolve b5e2562 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2562
          have b5e2564 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e2563
               have i₂ := b5e107
               grind)
            | exact superpose b5e107 b5e2563
            | exact resolve b5e2563 b5e107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e107 b5e2563
          have b5e2569 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 (M.op (σ x) (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b5e34 (σ x) (σ y) X1 X0
               have i₂ := b5e2564
               grind)
            | exact superpose b5e2564 b5e34
            | exact resolve b5e34 b5e2564
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e2581 : (M.op x y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e188 (σ x) (σ y)
               have i₂ := b5e2564
               grind)
            | exact superpose b5e2564 b5e188
            | exact resolve b5e188 b5e2564
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e188
          have b5e2582 : (M.op x y) = (σ y) := by
            first
            | (have i₁ := b5e2581
               have i₂ := b5e2564
               grind)
            | exact superpose b5e2564 b5e2581
            | exact resolve b5e2581 b5e2564
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2581
          have b5e2593 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e2569 X0 X1
               have i₂ := b5e2564
               grind)
            | exact superpose b5e2564 b5e2569
            | exact resolve b5e2569 b5e2564
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2564 b5e2569
          have b5e2604 : ∀ X1 : G, (M.op x y) = (M.op X1 (σ y)) := by
            intro X1
            first
            | (have i₁ := b5e2593 x X1
               have i₂ := b5e167 x X1
               grind)
            | exact superpose b5e167 b5e2593
            | exact resolve b5e2593 b5e167
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e167 b5e2593
          have b5e2607 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
            intro X1
            first
            | (have i₁ := b5e2604 X1
               have i₂ := b5e2582
               grind)
            | exact superpose b5e2582 b5e2604
            | exact resolve b5e2604 b5e2582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2582 b5e2604
          have b5e3960 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e2607 (σ y)
               grind)
            | exact superpose b5e2607 b5e23
            | (have r₁ := b5e23
               have r₂ := b5e2607 (σ y)
               grind)
            | exact resolve b5e23 b5e2607
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2607
          have b5e3965 : False := by grind
          exact b5e3965
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e50 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b6e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e50 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e55 : ∀ X0 X1 : G, (k X0 (σ y)) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e51 X0
             grind)
          | exact superpose b6e51 b6e15
          | (have j0 := b6e15 X1 X0
             grind)
          | exact resolve b6e15 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e102 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (σ y)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          grind
        clear b6e51
        have b6e106 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b6e102 X0
             have j1 := b6e55 (M.op X0 X0) X0
             grind)
          | (have r₁ := b6e102 X0
             have r₂ := b6e55 (M.op X0 X0) x
             grind)
          | exact resolve b6e102 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55 b6e102
        have b6e114 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e106 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e106
          | exact resolve b6e106 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e106
        have b6e121 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e114
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e114
          | exact resolve b6e114 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e114
        have b6e134 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e121
             grind)
          | exact superpose b6e121 b6e13
          | exact resolve b6e13 b6e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e121
        have b6e136 : y = (k y y) := by
          first
          | (have i₁ := b6e134
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e134
          | exact resolve b6e134 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e134
        have b6e157 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e136
             grind)
          | exact superpose b6e136 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e136
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e136
        have b6e158 : y = (M.op y y) := by grind
        clear b6e157
        have b6e160 : False := by grind
        exact b6e160
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e94 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          have b7e107 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e94
               have r₂ := b7e23
               grind)
            | exact resolve b7e94 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e108 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e107
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e107
            | exact resolve b7e107 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e107
          have b7e114 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e108
               grind)
            | exact superpose b7e108 b7e14
            | exact resolve b7e14 b7e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e108
          have b7e115 : y = (k x y) := by
            first
            | (have i₁ := b7e114
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e114
            | exact resolve b7e114 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e114
          have b7e155 : y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e115
               grind)
            | exact superpose b7e115 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e115
          have b7e156 : y = (M.op x y) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e155
               have r₂ := b7e21
               grind)
            | exact resolve b7e155 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e155
          have b7e158 : y = (M.op x y) := by
            first
            | (have r₁ := b7e156
               have r₂ := b7e22
               grind)
            | exact resolve b7e156 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e156
          have b7e212 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 x y X0
               have i₂ := b7e158
               grind)
            | exact superpose b7e158 b7e13
            | exact resolve b7e13 b7e158
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e213 : ∀ X0 : G, y = (M.op X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b7e212 X0
               have i₂ := b7e158
               grind)
            | exact superpose b7e158 b7e212
            | exact resolve b7e212 b7e158
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e212
          have b7e335 : y = (M.op y y) := by
            first
            | (have i₁ := b7e213 y
               have i₂ := b7e158
               grind)
            | exact superpose b7e158 b7e213
            | exact resolve b7e213 b7e158
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e158 b7e213
          have b7e381 : False := by grind
          exact b7e381
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e69 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
          have b8e1325 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e69 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69
          have b8e1326 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1325
               have r₂ := b8e23
               grind)
            | exact resolve b8e1325 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1325
          have b8e1327 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1326
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1326
            | exact resolve b8e1326 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1326
          have b8e1328 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1327
               grind)
            | exact superpose b8e1327 b8e20
            | exact resolve b8e20 b8e1327
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1327
          have b8e1602 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e1328
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1328
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e1328 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1328
          have b8e1603 : y = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e1602
          have b8e1606 : y = (M.op x x) := by
            first
            | (have r₁ := b8e1603
               have r₂ := b8e21
               grind)
            | exact resolve b8e1603 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1603
          have b8e1609 : False := by grind
          exact b8e1609

/-- `Equation4325`: `x ◇ (y ◇ x) = y ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,X),X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_ppxxx_y_pxx_pxy_Equation4325 :
    AutBox.GuardAut (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4325 := by
  classical
  refine AutBox.guardAut_of (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4325.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a a) a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op (M.op a a) a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x x) x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 (M.op X2 X2)) := by
        intro X0 X1 X2
        grind
      have b0e13 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op (M.op x x) x) := by grind
      have b0e18 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e22 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 X2) (M.op X0 (M.op X1 X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 (M.op X0 X2) X2 X3
           have i₂ := b0e10 X2 X0 X1
           grind)
        | (have i₁ := b0e10 (M.op X2 X2) X1 X2
           have i₂ := b0e10 X0 X1 X2
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X3 X3)) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 (M.op X2 X2) X1 X3
           have i₂ := b0e10 X0 X1 X2
           grind)
        | (have i₁ := b0e10 (M.op X1 X0) X0 X2
           have i₂ := b0e10 X0 X1 X2
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e24 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X3 X3)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e10 x X0 X3
           have i₂ := b0e10 x X0 X1
           grind)
        | (have i₁ := b0e10 x x x
           have i₂ := b0e10 X0 x x
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e26 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op X3 (M.op X0 (M.op (M.op X1 X1) X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X2 X3 (M.op X1 X1)
           have i₂ := b0e10 X0 (M.op X1 X1) X1
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e28 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X0 X1 x
           have i₂ := b0e10 X2 X1 x
           grind)
        | (have i₁ := b0e10 X0 X0 X0
           have i₂ := b0e10 X0 X0 X2
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e10 (σ x) (M.op (σ x) (σ x)) X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : (M.op x x) = (k x y) := by grind
      have b0e44 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      have b0e47 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e44
           have i₂ := b0e15 x y
           grind)
        | exact superpose b0e15 b0e44
        | exact resolve b0e44 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e48 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e47
           have i₂ := b0e43
           grind)
        | exact superpose b0e43 b0e47
        | exact resolve b0e47 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e47
      have b0e55 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        grind
      have b0e145 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op x x) X0)) := by
        intro X0
        first
        | (have i₁ := b0e28 X0 (M.op x x) x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e28
        | exact resolve b0e28 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e235 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e55 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e250 : (M.op x y) = (M.op (M.op (M.op x x) (M.op x x)) (M.op x y)) := by
        first
        | (have i₁ := b0e145 (M.op (M.op x x) (M.op x x))
           have i₂ := b0e145 (M.op x x)
           grind)
        | exact superpose b0e145 b0e145
        | exact resolve b0e145 b0e145
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e262 : ∀ X0 : G, (M.op x y) = (M.op (M.op x x) (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e24 (M.op x x) (M.op x x) X0
           have i₂ := b0e145 (M.op x x)
           grind)
        | exact superpose b0e145 b0e24
        | exact resolve b0e24 b0e145
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24 b0e145
      have b0e267 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
        first
        | (have i₁ := b0e250
           have i₂ := b0e262 x
           grind)
        | exact superpose b0e262 b0e250
        | exact resolve b0e250 b0e262
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e250
      have b0e404 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op x y) (M.op (M.op x x) (M.op X2 X2))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e22 (M.op x x) X2 (M.op X0 X0) X1
           have i₂ := b0e262 X0
           grind)
        | exact superpose b0e262 b0e22
        | exact resolve b0e22 b0e262
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e411 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op x y) (M.op x y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e404 X0 X1 x
           have i₂ := b0e262 x
           grind)
        | exact superpose b0e262 b0e404
        | exact resolve b0e404 b0e262
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e404
      have b0e412 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e411 X0 X1
           have i₂ := b0e267
           grind)
        | exact superpose b0e267 b0e411
        | exact resolve b0e411 b0e267
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e267 b0e411
      have b0e679 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (M.op (M.op X2 X2) (M.op X3 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e23 x (M.op X2 X2) X1 X3
           have i₂ := b0e26 x X2 X0 (M.op X1 X1)
           grind)
        | exact superpose b0e26 b0e23
        | exact resolve b0e23 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e26
      have b0e704 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e679 X0 X1 x x
           have i₂ := b0e412 x x
           grind)
        | exact superpose b0e412 b0e679
        | exact resolve b0e679 b0e412
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e412 b0e679
      have b0e746 : (M.op x y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e704 (σ x) (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e704
        | exact resolve b0e704 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e704
      have b0e837 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
        first
        | (have i₁ := b0e33 (σ x)
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e33
        | exact resolve b0e33 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e48
      have b0e920 : (M.op x y) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
        first
        | (have i₁ := b0e837
           have i₂ := b0e746
           grind)
        | exact superpose b0e746 b0e837
        | exact resolve b0e837 b0e746
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e837
      have b0e959 : (M.op x y) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e746
           grind)
        | exact superpose b0e746 b0e16
        | exact resolve b0e16 b0e746
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e746
      have b0e6228 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (σ (M.op x x)) (σ (M.op x x))) := by
        first
        | (have i₁ := b0e235 (σ (M.op x x)) (σ (M.op x x))
           have i₂ := b0e920
           grind)
        | exact superpose b0e920 b0e235
        | exact resolve b0e235 b0e920
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e920
      have b0e6239 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e235 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e235
      have b0e6241 : (M.op x y) = (k (σ (M.op x x)) (σ (M.op x x))) := by grind
      clear b0e6228
      have b0e6249 : (M.op x y) = (σ (k (M.op x x) (M.op x x))) := by
        first
        | (have i₁ := b0e6241
           have i₂ := b0e15 (M.op x x) (M.op x x)
           grind)
        | exact superpose b0e15 b0e6241
        | exact resolve b0e6241 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6241
      have b0e6293 : (M.op x y) = (σ (M.op (M.op x x) (M.op x x))) := by
        first
        | (have i₁ := b0e6249
           have i₂ := b0e6239 (M.op x x)
           grind)
        | exact superpose b0e6239 b0e6249
        | exact resolve b0e6249 b0e6239
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6239 b0e6249
      have b0e6310 : (M.op x y) = (σ (M.op x y)) := by
        first
        | (have i₁ := b0e6293
           have i₂ := b0e262 x
           grind)
        | exact superpose b0e262 b0e6293
        | exact resolve b0e6293 b0e262
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e262 b0e6293
      have b0e6314 : False := by grind
      exact b0e6314
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 (M.op X2 X2)) := by
        intro X0 X1 X2
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e17 : y = (M.op (M.op x x) x) := by grind
      have b1e18 : (σ y) ≠ (M.op (M.op (σ x) (σ x)) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e20 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b1e26 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op X3 (M.op X0 (M.op (M.op X1 X1) X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X2 X3 (M.op X1 X1)
           have i₂ := b1e10 X0 (M.op X1 X1) X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e31 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e15 (k (τ X0) X1) X2
           have i₂ := b1e20 X0 X1
           grind)
        | exact superpose b1e20 b1e15
        | exact resolve b1e15 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20
      have b1e50 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        grind
      have b1e52 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X2 X2) (M.op X2 X2)) X1)) = X0 ∨ (k (M.op X2 X2) X0) = (M.op (M.op X2 X2) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 X1 (M.op (M.op X2 X2) (M.op X2 X2)) X2
           have i₂ := b1e14 (M.op X2 X2) X0
           grind)
        | (have i₁ := b1e10 X0 X1 X2
           have i₂ := b1e14 X0 (M.op X1 (M.op X2 X2))
           grind)
        | exact superpose b1e14 b1e10
        | (have j1 := b1e14 (M.op X2 X2) X0
           grind)
        | exact resolve b1e10 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e194 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b1e50 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e50
      have b1e2239 : ∀ X0 X1 X2 X4 : G, (M.op X2 X0) = (M.op X1 (M.op X2 X1)) ∨ (M.op (M.op X4 X4) X0) = (k (M.op X4 X4) X0) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b1e26 x (M.op X4 X4) X1 X2
           have i₂ := b1e52 X0 x X4
           grind)
        | (have i₁ := b1e26 X0 X1 X2 x
           have i₂ := b1e52 (M.op X0 (M.op (M.op X1 X1) X0)) X1 X2
           grind)
        | exact superpose b1e52 b1e26
        | (have j1 := b1e52 X0 X1 X4
           grind)
        | exact resolve b1e26 b1e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e26 b1e52
      have b1e2613 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X0)) ≠ (M.op (M.op X1 X1) X2) ∨ (k (M.op X1 X1) X2) = (M.op (M.op X1 X1) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e194 (M.op X1 X1) X2
           have i₂ := b1e10 X0 (M.op X1 X1) X1
           grind)
        | exact superpose b1e10 b1e194
        | (have j0 := b1e194 (M.op X1 X1) X2
           grind)
        | (have r₁ := b1e194 (M.op X2 X2) (M.op (M.op X2 X2) (M.op X2 X2))
           have r₂ := b1e10 (M.op X2 X2) (M.op X2 X2) X2
           grind)
        | exact resolve b1e194 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e2646 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b1e194 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e194
      have b1e2664 : ∀ X1 X2 : G, (k (M.op X1 X1) X2) = (M.op (M.op X1 X1) X2) := by
        intro X1 X2
        first
        | (have j0 := b1e2613 x X1 X2
           have j1 := b1e2239 X2 X1 X2 X1
           grind)
        | (have r₁ := b1e2613 X2 X1 (M.op X2 (M.op X1 X1))
           have r₂ := b1e2239 (M.op (M.op X1 X1) X2) (M.op X1 X1) X2 x
           grind)
        | (have r₁ := b1e2613 X1 X1 x
           have r₂ := b1e2239 x X1 (M.op X1 X1) x
           grind)
        | exact resolve b1e2613 b1e2239
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2239 b1e2613
      have b1e2694 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b1e15 X0 X0
           have i₂ := b1e2646 (σ X0)
           grind)
        | exact superpose b1e2646 b1e15
        | exact resolve b1e15 b1e2646
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e2701 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b1e2694 X0
           have i₂ := b1e2646 X0
           grind)
        | exact superpose b1e2646 b1e2694
        | exact resolve b1e2694 b1e2646
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2694
      have b1e2924 : (σ y) ≠ (M.op (σ (M.op x x)) (σ x)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e2701 x
           grind)
        | exact superpose b1e2701 b1e18
        | exact resolve b1e18 b1e2701
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e3063 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (k (M.op (σ X0) (σ X0)) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e31 (σ X0) X0 X1
           have i₂ := b1e2646 (σ X0)
           grind)
        | exact superpose b1e2646 b1e31
        | exact resolve b1e31 b1e2646
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e31
      have b1e3102 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (M.op (M.op (σ X0) (σ X0)) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e3063 X0 X1
           have i₂ := b1e2664 (σ X0) (σ X1)
           grind)
        | exact superpose b1e2664 b1e3063
        | exact resolve b1e3063 b1e2664
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3063
      have b1e3108 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e3102 X0 X1
           have i₂ := b1e2701 X0
           grind)
        | exact superpose b1e2701 b1e3102
        | exact resolve b1e3102 b1e2701
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2701 b1e3102
      have b1e3109 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (k (k X0 X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e3108 X0 X1
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e3108
        | exact resolve b1e3108 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3108
      have b1e3110 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (k (M.op X0 X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e3109 X0 X1
           have i₂ := b1e2646 X0
           grind)
        | exact superpose b1e2646 b1e3109
        | exact resolve b1e3109 b1e2646
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2646 b1e3109
      have b1e3111 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e3110 X0 X1
           have i₂ := b1e2664 X0 X1
           grind)
        | exact superpose b1e2664 b1e3110
        | exact resolve b1e3110 b1e2664
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2664 b1e3110
      have b1e209361 : (σ y) ≠ (σ (M.op (M.op x x) x)) := by
        first
        | (have i₁ := b1e2924
           have i₂ := b1e3111 x x
           grind)
        | exact superpose b1e3111 b1e2924
        | exact resolve b1e2924 b1e3111
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2924 b1e3111
      have b1e209839 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e209361
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e209361
        | exact resolve b1e209361 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e209361
      have b1e209840 : False := by grind
      exact b1e209840
  · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 (M.op X2 X2)) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b2e17 : y ≠ (M.op (M.op x x) x) := by grind
      have b2e18 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e20 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 (τ X0) X1
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e15
        | exact resolve b2e15 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e26 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op X3 (M.op X0 (M.op (M.op X1 X1) X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X2 X3 (M.op X1 X1)
           have i₂ := b2e10 X0 (M.op X1 X1) X1
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e31 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e15 (k (τ X0) X1) X2
           have i₂ := b2e20 X0 X1
           grind)
        | exact superpose b2e20 b2e15
        | exact resolve b2e15 b2e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e20
      have b2e44 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
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
      have b2e47 : (σ y) = (M.op (σ (k x y)) (σ x)) := by
        first
        | (have i₁ := b2e18
           have i₂ := b2e46
           grind)
        | exact superpose b2e46 b2e18
        | exact resolve b2e18 b2e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e57 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        grind
      have b2e58 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 X1 (M.op X1 X1) X2
           have i₂ := b2e14 X1 X0
           grind)
        | (have i₁ := b2e10 X0 X1 X2
           have i₂ := b2e14 X0 (M.op X1 X0)
           grind)
        | exact superpose b2e14 b2e10
        | (have j1 := b2e14 X1 X0
           grind)
        | exact resolve b2e10 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e59 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X2 X2) (M.op X2 X2)) X1)) = X0 ∨ (k (M.op X2 X2) X0) = (M.op (M.op X2 X2) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 X1 (M.op (M.op X2 X2) (M.op X2 X2)) X2
           have i₂ := b2e14 (M.op X2 X2) X0
           grind)
        | (have i₁ := b2e10 X0 X1 X2
           have i₂ := b2e14 X0 (M.op X1 (M.op X2 X2))
           grind)
        | exact superpose b2e14 b2e10
        | (have j1 := b2e14 (M.op X2 X2) X0
           grind)
        | exact resolve b2e10 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e61 : ∀ X0 : G, y ≠ X0 ∨ (k x X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b2e17
           have i₂ := b2e14 x X0
           grind)
        | (have i₁ := b2e17
           have i₂ := b2e14 X0 (M.op (M.op x x) x)
           grind)
        | exact superpose b2e14 b2e17
        | (have j1 := b2e14 x X0
           grind)
        | (have r₁ := b2e17
           have r₂ := b2e14 x y
           grind)
        | exact resolve b2e17 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e66 : (M.op x y) = (k x y) := by
        first
        | (have j0 := b2e61 y
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e61
      have b2e211 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b2e57 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e217 : (σ y) = (M.op (σ (M.op x y)) (σ x)) := by
        first
        | (have i₁ := b2e47
           have i₂ := b2e66
           grind)
        | exact superpose b2e66 b2e47
        | exact resolve b2e47 b2e66
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e221 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (k x y)) (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b2e10 (σ x) (σ (k x y)) X0
           have i₂ := b2e47
           grind)
        | exact superpose b2e47 b2e10
        | exact resolve b2e10 b2e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47
      have b2e222 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b2e221 X0
           have i₂ := b2e66
           grind)
        | exact superpose b2e66 b2e221
        | exact resolve b2e221 b2e66
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e221
      have b2e1172 : ∀ X0 : G, (σ (k x y)) = (M.op (σ (k x y)) (M.op X0 X0)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e58 (σ x) (σ x) x
           have i₂ := b2e46
           grind)
        | exact superpose b2e46 b2e58
        | exact resolve b2e58 b2e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46 b2e58
      have b2e1375 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 X0)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e1172 X0
           have i₂ := b2e66
           grind)
        | exact superpose b2e66 b2e1172
        | exact resolve b2e1172 b2e66
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1172
      have b2e1423 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
        first
        | (have i₁ := b2e1375 x
           have i₂ := b2e222 x
           grind)
        | exact superpose b2e222 b2e1375
        | exact resolve b2e1375 b2e222
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e222 b2e1375
      have b2e1433 : (σ (k x y)) = (k (σ x) (σ x)) := by
        first
        | (have r₁ := b2e1423
           have r₂ := b2e16
           grind)
        | exact resolve b2e1423 b2e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1423
      have b2e1439 : (σ (k x y)) = (σ (k x x)) := by
        first
        | (have i₁ := b2e1433
           have i₂ := b2e15 x x
           grind)
        | exact superpose b2e15 b2e1433
        | exact resolve b2e1433 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1433
      have b2e1440 : (σ (M.op x y)) = (σ (k x x)) := by
        first
        | (have i₁ := b2e1439
           have i₂ := b2e66
           grind)
        | exact superpose b2e66 b2e1439
        | exact resolve b2e1439 b2e66
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e66 b2e1439
      have b2e1447 : (k x x) = (τ (σ (M.op x y))) := by
        first
        | (have i₁ := b2e11 (k x x)
           have i₂ := b2e1440
           grind)
        | exact superpose b2e1440 b2e11
        | exact resolve b2e11 b2e1440
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1440
      have b2e1448 : (M.op x y) = (k x x) := by
        first
        | (have i₁ := b2e1447
           have i₂ := b2e11 (M.op x y)
           grind)
        | exact superpose b2e11 b2e1447
        | exact resolve b2e1447 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1447
      have b2e1558 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b2e57 x x
           have i₂ := b2e1448
           grind)
        | exact superpose b2e1448 b2e57
        | exact resolve b2e57 b2e1448
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e57 b2e1448
      have b2e1559 : (M.op x y) = (M.op x x) := by grind
      clear b2e1558
      have b2e1766 : (σ y) = (M.op (σ (M.op x x)) (σ x)) := by
        first
        | (have i₁ := b2e217
           have i₂ := b2e1559
           grind)
        | exact superpose b2e1559 b2e217
        | exact resolve b2e217 b2e1559
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e217 b2e1559
      have b2e2522 : ∀ X0 X1 X2 X4 : G, (M.op X2 X0) = (M.op X1 (M.op X2 X1)) ∨ (M.op (M.op X4 X4) X0) = (k (M.op X4 X4) X0) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b2e26 x (M.op X4 X4) X1 X2
           have i₂ := b2e59 X0 x X4
           grind)
        | (have i₁ := b2e26 X0 X1 X2 x
           have i₂ := b2e59 (M.op X0 (M.op (M.op X1 X1) X0)) X1 X2
           grind)
        | exact superpose b2e59 b2e26
        | (have j1 := b2e59 X0 X1 X4
           grind)
        | exact resolve b2e26 b2e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e26 b2e59
      have b2e4408 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X0)) ≠ (M.op (M.op X1 X1) X2) ∨ (k (M.op X1 X1) X2) = (M.op (M.op X1 X1) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e211 (M.op X1 X1) X2
           have i₂ := b2e10 X0 (M.op X1 X1) X1
           grind)
        | exact superpose b2e10 b2e211
        | (have j0 := b2e211 (M.op X1 X1) X2
           grind)
        | (have r₁ := b2e211 (M.op X2 X2) (M.op (M.op X2 X2) (M.op X2 X2))
           have r₂ := b2e10 (M.op X2 X2) (M.op X2 X2) X2
           grind)
        | exact resolve b2e211 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e4456 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b2e211 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e211
      have b2e4484 : ∀ X1 X2 : G, (k (M.op X1 X1) X2) = (M.op (M.op X1 X1) X2) := by
        intro X1 X2
        first
        | (have j0 := b2e4408 x X1 X2
           have j1 := b2e2522 X2 X1 X2 X1
           grind)
        | (have r₁ := b2e4408 X2 X1 (M.op X2 (M.op X1 X1))
           have r₂ := b2e2522 (M.op (M.op X1 X1) X2) (M.op X1 X1) X2 x
           grind)
        | (have r₁ := b2e4408 X1 X1 x
           have r₂ := b2e2522 x X1 (M.op X1 X1) x
           grind)
        | exact resolve b2e4408 b2e2522
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2522 b2e4408
      have b2e4546 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b2e15 X0 X0
           have i₂ := b2e4456 (σ X0)
           grind)
        | exact superpose b2e4456 b2e15
        | exact resolve b2e15 b2e4456
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e4555 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b2e4546 X0
           have i₂ := b2e4456 X0
           grind)
        | exact superpose b2e4456 b2e4546
        | exact resolve b2e4546 b2e4456
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4546
      have b2e5107 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (k (M.op (σ X0) (σ X0)) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e31 (σ X0) X0 X1
           have i₂ := b2e4456 (σ X0)
           grind)
        | exact superpose b2e4456 b2e31
        | exact resolve b2e31 b2e4456
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e31
      have b2e5146 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (M.op (M.op (σ X0) (σ X0)) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e5107 X0 X1
           have i₂ := b2e4484 (σ X0) (σ X1)
           grind)
        | exact superpose b2e4484 b2e5107
        | exact resolve b2e5107 b2e4484
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e5107
      have b2e5157 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e5146 X0 X1
           have i₂ := b2e4555 X0
           grind)
        | exact superpose b2e4555 b2e5146
        | exact resolve b2e5146 b2e4555
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4555 b2e5146
      have b2e5161 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (k (k X0 X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e5157 X0 X1
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e5157
        | exact resolve b2e5157 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e5157
      have b2e5162 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (k (M.op X0 X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e5161 X0 X1
           have i₂ := b2e4456 X0
           grind)
        | exact superpose b2e4456 b2e5161
        | exact resolve b2e5161 b2e4456
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4456 b2e5161
      have b2e5163 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e5162 X0 X1
           have i₂ := b2e4484 X0 X1
           grind)
        | exact superpose b2e4484 b2e5162
        | exact resolve b2e5162 b2e4484
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4484 b2e5162
      have b2e162716 : (σ y) = (σ (M.op (M.op x x) x)) := by
        first
        | (have i₁ := b2e1766
           have i₂ := b2e5163 x x
           grind)
        | exact superpose b2e5163 b2e1766
        | exact resolve b2e1766 b2e5163
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1766 b2e5163
      have b2e170042 : (M.op (M.op x x) x) = (τ (σ y)) := by
        first
        | (have i₁ := b2e11 (M.op (M.op x x) x)
           have i₂ := b2e162716
           grind)
        | exact superpose b2e162716 b2e11
        | exact resolve b2e11 b2e162716
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e162716
      have b2e170078 : y = (M.op (M.op x x) x) := by
        first
        | (have i₁ := b2e170042
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e170042
        | exact resolve b2e170042 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e170042
      have b2e170082 : False := by grind
      exact b2e170082
    · have b3e14 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op (M.op x x) x) := by grind
      have b3e18 : (σ y) ≠ (M.op (M.op (σ x) (σ x)) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e59 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e14 (σ x) X0
           grind)
        | (have i₁ := b3e18
           have i₂ := b3e14 X0 (M.op (M.op (σ x) (σ x)) (σ x))
           grind)
        | exact superpose b3e14 b3e18
        | (have j1 := b3e14 (σ x) X0
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e14 (σ x) (σ y)
           grind)
        | exact resolve b3e18 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e60 : ∀ X0 : G, y ≠ X0 ∨ (k x X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b3e17
           have i₂ := b3e14 x X0
           grind)
        | (have i₁ := b3e17
           have i₂ := b3e14 X0 (M.op (M.op x x) x)
           grind)
        | exact superpose b3e14 b3e17
        | (have j1 := b3e14 x X0
           grind)
        | (have r₁ := b3e17
           have r₂ := b3e14 x y
           grind)
        | exact resolve b3e17 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e65 : (M.op x y) = (k x y) := by
        first
        | (have j0 := b3e60 y
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e60
      have b3e148 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b3e59 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e59
      have b3e149 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e148
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e148
        | exact resolve b3e148 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e148
      have b3e150 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b3e149
           have i₂ := b3e65
           grind)
        | exact superpose b3e65 b3e149
        | exact resolve b3e149 b3e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e65 b3e149
      have b3e151 : False := by grind
      exact b3e151

/-- `Equation4325`: `x ◇ (y ◇ x) = y ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation4325 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4325 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4325.models_iff G M).mp hM
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
      have b0e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e51 (σ X0)
           grind)
        | exact superpose b0e51 b0e17
        | exact resolve b0e17 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e62 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e57 X0
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e57
        | exact resolve b0e57 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51 b0e57
      have b0e299 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e62 x
           grind)
        | exact superpose b0e62 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e62 x
           grind)
        | exact resolve b0e22 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e62
      have b0e313 : False := by grind
      exact b0e313
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b1e59 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b1e62 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e64 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e62
        have b1e65 : (k x y) = (M.op y y) := by grind
        clear b1e59
        have b1e66 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e64
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e64
          | exact resolve b1e64 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64
        have b1e67 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e66
             have i₂ := b1e63 y
             grind)
          | exact superpose b1e63 b1e66
          | exact resolve b1e66 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66
        have b1e69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e63 (σ X0)
             grind)
          | exact superpose b1e63 b1e18
          | exact resolve b1e18 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e69 X0
             have i₂ := b1e63 X0
             grind)
          | exact superpose b1e63 b1e69
          | exact resolve b1e69 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63 b1e69
        have b1e84 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b1e86 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e84 X0
             have i₂ := b1e67
             grind)
          | exact superpose b1e67 b1e84
          | (have j0 := b1e84 X0
             grind)
          | exact resolve b1e84 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e84
        have b1e146 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e67
             grind)
          | exact superpose b1e67 b1e23
          | exact resolve b1e23 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e3634 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e86 (σ x)
             have i₂ := b1e67
             grind)
          | exact superpose b1e67 b1e86
          | (have j0 := b1e86 (σ x)
             grind)
          | (have r₁ := b1e86 (σ x)
             have r₂ := b1e67
             grind)
          | exact resolve b1e86 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67 b1e86
        have b1e3635 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e3634
        have b1e3636 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e3635
             have i₂ := b1e76 x
             grind)
          | exact superpose b1e76 b1e3635
          | exact resolve b1e3635 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3635
        have b1e3637 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e3636
             have r₂ := b1e146
             grind)
          | exact resolve b1e3636 b1e146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3636
        have b1e3638 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e3637
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e3637
          | exact resolve b1e3637 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3637
        have b1e3639 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e3638
             have i₂ := b1e65
             grind)
          | exact superpose b1e65 b1e3638
          | exact resolve b1e3638 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65 b1e3638
        have b1e3640 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e3639
             have i₂ := b1e76 x
             grind)
          | exact superpose b1e76 b1e3639
          | exact resolve b1e3639 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76 b1e3639
        have b1e3641 : False := by grind
        exact b1e3641
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e55 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b2e58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e59 : (k x y) = (M.op y y) := by grind
        clear b2e55
        have b2e61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e58 (σ X0)
             grind)
          | exact superpose b2e58 b2e18
          | exact resolve b2e18 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e61 X0
             have i₂ := b2e58 X0
             grind)
          | exact superpose b2e58 b2e61
          | exact resolve b2e61 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58 b2e61
        have b2e101 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
        have b2e164 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e68 y
             grind)
          | exact superpose b2e68 b2e22
          | exact resolve b2e22 b2e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68
        have b2e6132 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e101 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e101
        have b2e6133 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e6132
             have r₂ := b2e21
             grind)
          | exact resolve b2e6132 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6132
        have b2e6134 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e6133
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e6133
          | exact resolve b2e6133 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6133
        have b2e6135 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e6134
             have i₂ := b2e59
             grind)
          | exact superpose b2e59 b2e6134
          | exact resolve b2e6134 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59 b2e6134
        have b2e6136 : False := by grind
        exact b2e6136
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b3e62 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        clear b3e62
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
        have b3e92 : (σ (k x y)) = (σ (k y y)) := by
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
        have b3e93 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e92
             have i₂ := b3e63 y
             grind)
          | exact superpose b3e63 b3e92
          | exact resolve b3e92 b3e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63 b3e92
        have b3e94 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e93
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e93
          | exact resolve b3e93 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e93
        have b3e356 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
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
        have b3e1468 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e83 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e83
        have b3e1469 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e1468
             have r₂ := b3e20
             grind)
          | exact resolve b3e1468 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1468
        have b3e1473 : (σ (M.op x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e94
             have i₂ := b3e1469
             grind)
          | exact superpose b3e1469 b3e94
          | exact resolve b3e94 b3e1469
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e94 b3e1469
        have b3e1477 : False := by grind
        exact b3e1477
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
          have b4e78 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e79 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e80 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e78
          have b4e82 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e80
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e80
            | exact resolve b4e80 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80
          have b4e84 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e82
               have i₂ := b4e79 y
               grind)
            | exact superpose b4e79 b4e82
            | exact resolve b4e82 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e79 b4e82
          have b4e85 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e84
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e84
            | exact resolve b4e84 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84
          have b4e86 : False := by grind
          exact b4e86
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
          have b5e74 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e78 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e74 (σ X0)
               grind)
            | exact superpose b5e74 b5e19
            | exact resolve b5e19 b5e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e87 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e78 X0
               have i₂ := b5e74 X0
               grind)
            | exact superpose b5e74 b5e78
            | exact resolve b5e78 b5e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e74 b5e78
          have b5e96 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e143 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e1614 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e96 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e96
          have b5e1615 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e1614
               have r₂ := b5e21
               grind)
            | exact resolve b5e1614 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1614
          have b5e10641 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e143 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e143
          have b5e10642 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e10641
               have r₂ := b5e23
               grind)
            | exact resolve b5e10641 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10641
          have b5e10643 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e10642
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e10642
            | exact resolve b5e10642 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10642
          have b5e10644 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e10643
               have i₂ := b5e1615
               grind)
            | exact superpose b5e1615 b5e10643
            | exact resolve b5e10643 b5e1615
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1615 b5e10643
          have b5e10647 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e10644
               grind)
            | exact superpose b5e10644 b5e23
            | exact resolve b5e23 b5e10644
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10644
          have b5e10681 : False := by grind
          exact b5e10681
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
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
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e57 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        clear b6e57
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
          have b7e72 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
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
          clear b7e72
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
          have b7e125 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e148 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e125 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e125
          have b7e4507 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e4509 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e4507
          have b7e4510 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e4509
               have i₂ := b7e87 x
               grind)
            | exact superpose b7e87 b7e4509
            | exact resolve b7e4509 b7e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4509
          have b7e4511 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e4510
               have r₂ := b7e105
               grind)
            | exact resolve b7e4510 b7e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4510
          have b7e4512 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e4511
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e4511
            | exact resolve b7e4511 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4511
          have b7e4513 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e4512
               have i₂ := b7e87 x
               grind)
            | exact superpose b7e87 b7e4512
            | exact resolve b7e4512 b7e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87 b7e4512
          have b7e4515 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e4513
               have i₂ := b7e148 x y
               grind)
            | exact superpose b7e148 b7e4513
            | (have j1 := b7e148 x y
               grind)
            | exact resolve b7e4513 b7e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e148
          have b7e4522 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e4513
               grind)
            | exact superpose b7e4513 b7e14
            | exact resolve b7e14 b7e4513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4513
          have b7e4523 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e4522
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e4522
            | exact resolve b7e4522 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4522
          have b7e4530 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e4515
               have r₂ := b7e105
               grind)
            | exact resolve b7e4515 b7e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105 b7e4515
          have b7e4533 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e4530
               have r₂ := b7e22
               grind)
            | exact resolve b7e4530 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4530
          have b7e4534 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e4533
               have i₂ := b7e4523
               grind)
            | exact superpose b7e4523 b7e4533
            | exact resolve b7e4533 b7e4523
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4523 b7e4533
          have b7e4535 : False := by grind
          exact b7e4535
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e7819 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e134 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e134
          have b8e7820 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e7819
               have r₂ := b8e23
               grind)
            | exact resolve b8e7819 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7819
          have b8e7821 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e7820
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e7820
            | exact resolve b8e7820 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7820
          have b8e7826 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e7821
               grind)
            | exact superpose b8e7821 b8e20
            | exact resolve b8e20 b8e7821
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7821
          have b8e8076 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e7826
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e7826
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e7826 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7826
          have b8e8077 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e8076
          have b8e8079 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e8077
               have r₂ := b8e21
               grind)
            | exact resolve b8e8077 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8077
          have b8e8082 : False := by grind
          exact b8e8082

/-- `Equation4331`: `x ◇ (y ◇ x) = z ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_pxx_pxx_pxy_Equation4331 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4331 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4331.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
      have b0e32 : ∀ X0 : G, (M.op x y) = (M.op X0 y) := by
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
      have b0e39 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X0)) = (M.op X1 (σ y)) := by
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
      have b0e44 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e32 X1
           have i₂ := b0e32 X0
           grind)
        | (have i₁ := b0e32 X0
           have i₂ := b0e32 x
           grind)
        | exact superpose b0e32 b0e32
        | exact resolve b0e32 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X0 X1 : G, (M.op X1 (M.op x x)) = (M.op y (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 y x X1
           have i₂ := b0e32 X0
           grind)
        | (have i₁ := b0e11 y X0 x
           have i₂ := b0e32 X0
           grind)
        | exact superpose b0e32 b0e11
        | exact resolve b0e11 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e49 : ∀ X0 X1 : G, (M.op X1 y) = (M.op y (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e45 X0 X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e45
        | exact resolve b0e45 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
      have b0e167 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op X0 y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 y X1 X2
           have i₂ := b0e49 X1 X0
           grind)
        | exact superpose b0e49 b0e11
        | exact resolve b0e11 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e286 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e49 (σ x) X1
           have i₂ := b0e39 y X0
           grind)
        | exact superpose b0e39 b0e49
        | exact resolve b0e49 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e49
      have b0e325 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e286 (σ x) X0
           grind)
        | exact superpose b0e286 b0e18
        | exact resolve b0e18 b0e286
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e286
      have b0e442 : ∀ X0 X1 : G, (M.op X1 y) ≠ (σ (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e325 X1
           have i₂ := b0e44 x X0
           grind)
        | (have i₁ := b0e325 X1
           have i₂ := b0e44 X0 x
           grind)
        | exact superpose b0e44 b0e325
        | exact resolve b0e325 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e325
      have b0e1267 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op X1 (M.op X0 y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e167 X2 y X1
           have i₂ := b0e44 y X0
           grind)
        | (have i₁ := b0e167 X2 y X1
           have i₂ := b0e44 X0 y
           grind)
        | exact superpose b0e44 b0e167
        | exact resolve b0e167 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e1343 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) ≠ (σ (M.op X3 y)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e442 X3 x
           have i₂ := b0e167 x X1 X0
           grind)
        | exact superpose b0e167 b0e442
        | exact resolve b0e442 b0e167
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e167 b0e442
      have b0e1951 : ∀ X0 X1 : G, (M.op X0 y) = (k (M.op X1 y) (M.op X0 y)) := by
        intro X0 X1
        grind
      clear b0e1267
      have b0e5536 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e95 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e95
      have b0e5537 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e5536 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5536
      have b0e79455 : ∀ X0 : G, (σ (M.op X0 y)) ≠ (σ (M.op X0 y)) ∨ (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b0e5537 (M.op X0 y)
           have i₂ := b0e1951 X0 X0
           grind)
        | exact superpose b0e1951 b0e5537
        | (have j0 := b0e5537 (M.op X0 y)
           grind)
        | exact resolve b0e5537 b0e1951
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1951 b0e5537
      have b0e79465 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) := by
        intro X0
        first
        | (have j0 := b0e79455 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79455
      have b0e587091 : ∀ X0 X1 X2 : G, (σ (M.op X2 y)) ≠ (M.op X1 (σ (M.op X0 y))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1343 X1 (σ (M.op X0 y)) X2
           have i₂ := b0e79465 X0
           grind)
        | exact superpose b0e79465 b0e1343
        | exact resolve b0e1343 b0e79465
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1343
      have b0e587127 : ∀ X0 X1 : G, (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) = (M.op X1 (σ (M.op X0 y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ (M.op X0 y)) (σ (M.op X0 y)) x
           have i₂ := b0e79465 X0
           grind)
        | exact superpose b0e79465 b0e11
        | exact resolve b0e11 b0e79465
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e587229 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (M.op X1 (σ (M.op X0 y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e587127 X0 X1
           have i₂ := b0e79465 X0
           grind)
        | exact superpose b0e79465 b0e587127
        | exact resolve b0e587127 b0e79465
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79465 b0e587127
      have b0e587277 : False := by
        have f587277_10 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (M.op X1 (σ (M.op X0 y))) := by
          intro X0 X1
          grind
        have f587277_11 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 y))) ≠ (σ (M.op X2 y)) := by
          intro X0 X1 X2
          grind
        have f587277_20 : False := by
          first
          | (have r₁ := f587277_10 x x
             have r₂ := f587277_11 x x x
             grind)
          | exact resolve f587277_10 f587277_11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        exact f587277_20
      exact b0e587277
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b1e35 : ∀ X0 : G, (M.op x y) = (M.op X0 y) := by
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
        have b1e36 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
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
        have b1e41 : ∀ X0 X1 : G, (M.op X0 (M.op x X0)) = (M.op X1 y) := by
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
        have b1e47 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e36 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e36
          | exact resolve b1e36 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e60 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (σ y) X0 X1
             have i₂ := b1e47 X0
             grind)
          | exact superpose b1e47 b1e12
          | exact resolve b1e12 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e62 : ∀ X0 X1 : G, (σ y) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e60 X0 X1
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e60
          | exact resolve b1e60 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e90 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
        have b1e93 : y = (M.op y y) := by grind
        clear b1e90
        have b1e114 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X2 (M.op x x)) := by
          intro X0 X2
          first
          | (have i₁ := b1e12 x x X2
             have i₂ := b1e41 x X0
             grind)
          | exact superpose b1e41 b1e12
          | exact resolve b1e12 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e121 : ∀ X0 : G, (σ y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e114 X0 x
             have i₂ := b1e62 x x
             grind)
          | exact superpose b1e62 b1e114
          | exact resolve b1e114 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62 b1e114
        have b1e139 : y = (σ y) := by
          first
          | (have i₁ := b1e93
             have i₂ := b1e121 y
             grind)
          | exact superpose b1e121 b1e93
          | exact resolve b1e93 b1e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e93
        have b1e154 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e139
             grind)
          | exact superpose b1e139 b1e19
          | exact resolve b1e19 b1e139
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e159 : (M.op x y) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e154
             have i₂ := b1e35 (σ x)
             grind)
          | exact superpose b1e35 b1e154
          | exact resolve b1e154 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35 b1e154
        have b1e160 : (σ y) ≠ (σ (σ y)) := by
          first
          | (have i₁ := b1e159
             have i₂ := b1e121 x
             grind)
          | exact superpose b1e121 b1e159
          | exact resolve b1e159 b1e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e121 b1e159
        have b1e161 : y ≠ (σ y) := by
          first
          | (have i₁ := b1e160
             have i₂ := b1e139
             grind)
          | exact superpose b1e139 b1e160
          | exact resolve b1e160 b1e139
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e160
        have b1e162 : False := by grind
        exact b1e162
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b2e24 : y = (k x y) := by grind
        have b2e70 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
        have b2e85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b2e1951 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e70 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e1952 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1951
             have r₂ := b2e22
             grind)
          | exact resolve b2e1951 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1951
        have b2e1953 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1952
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1952
          | exact resolve b2e1952 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1952
        have b2e1954 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1953
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1953
          | exact resolve b2e1953 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1953
        have b2e5117 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e85 x x
             grind)
          | exact superpose b2e85 b2e21
          | (have j1 := b2e85 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e85 x y
             grind)
          | exact resolve b2e21 b2e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e85
        have b2e5315 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e5117
        have b2e48513 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e5315
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e5315
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e5315 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5315
        have b2e48523 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e48513
        have b2e48538 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e48523
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e48523
          | exact resolve b2e48523 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48523
        have b2e48539 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e48538
        have b2e48551 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e48539
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e48539
          | exact resolve b2e48539 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48539
        have b2e48570 : (σ x) ≠ (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e48551
             grind)
          | exact superpose b2e48551 b2e21
          | exact resolve b2e21 b2e48551
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e48575 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by grind
        clear b2e48551
        have b2e48702 : (σ x) = (σ (k x x)) ∨ x = y := by
          first
          | (have i₁ := b2e48575
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e48575
          | exact resolve b2e48575 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48575
        have b2e50018 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e48702
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e48702
          | (have j1 := b2e17 x x
             grind)
          | exact resolve b2e48702 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48702
        have b2e50049 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) := by grind
        clear b2e50018
        have b2e50073 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e50049
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e50049
          | exact resolve b2e50049 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50049
        have b2e50083 : x = y ∨ x = (M.op x x) := by
          first
          | (have r₁ := b2e50073
             have r₂ := b2e48570
             grind)
          | exact resolve b2e50073 b2e48570
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48570 b2e50073
        have b2e50095 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e50083
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e50083
          | exact resolve b2e50083 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50083
        have b2e50096 : x = y := by grind
        clear b2e50095
        have b2e52325 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e1954
             have i₂ := b2e50096
             grind)
          | exact superpose b2e50096 b2e1954
          | exact resolve b2e1954 b2e50096
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1954 b2e50096
        have b2e52330 : False := by grind
        exact b2e52330
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : (σ y) = (k (σ x) (σ y)) := by grind
        have b3e26 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b3e25
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e25
          | exact resolve b3e25 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e31 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e26
             grind)
          | exact superpose b3e26 b3e13
          | exact resolve b3e13 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e32 : y = (k x y) := by
          first
          | (have i₁ := b3e31
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e31
          | exact resolve b3e31 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e35 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
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
        have b3e47 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e35 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e35
          | exact resolve b3e35 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e55 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b3e56 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ (M.op X0 X0) = y := by
          intro X0
          first
          | (have j0 := b3e55 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e1354 : y = (M.op x x) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b3e32
             have i₂ := b3e56 x
             grind)
          | exact superpose b3e56 b3e32
          | (have j1 := b3e56 x
             grind)
          | exact resolve b3e32 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32 b3e56
        have b3e1359 : y = (M.op x x) := by grind
        clear b3e1354
        have b3e1365 : False := by grind
        exact b3e1365
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e36 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
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
          have b4e37 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
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
          have b4e48 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e37 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e37
            | exact resolve b4e37 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e49 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e36 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e36
            | exact resolve b4e36 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e65 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e48 (σ x)
               grind)
            | exact superpose b4e48 b4e20
            | exact resolve b4e20 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e67 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e65
               have i₂ := b4e49 x
               grind)
            | exact superpose b4e49 b4e65
            | exact resolve b4e65 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49 b4e65
          have b4e68 : False := by grind
          exact b4e68
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : y = (k y y) := by grind
          have b5e96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
          have b5e4059 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e96 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e96
          have b5e4060 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e4059 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4059
          have b5e5911 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e4060 y
               have i₂ := b5e26
               grind)
            | exact superpose b5e26 b5e4060
            | (have j0 := b5e4060 y
               grind)
            | exact resolve b5e4060 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e4060
          have b5e5915 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e5911
          have b5e5921 : False := by grind
          exact b5e5921
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b6e24 : (σ y) = (k (σ x) (σ y)) := by grind
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
        have b6e39 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) := by
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
        have b6e60 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e19
             have i₂ := b6e39 X0
             grind)
          | (have i₁ := b6e19
             have i₂ := b6e39 (σ x)
             grind)
          | exact superpose b6e39 b6e19
          | exact resolve b6e19 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
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
        have b6e89 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
        have b6e91 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
          first
          | (have r₁ := b6e89
             have r₂ := b6e20
             grind)
          | exact resolve b6e89 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e89
        have b6e94 : (σ (M.op x y)) = (σ y) := by
          first
          | (have r₁ := b6e91
             have r₂ := b6e21
             grind)
          | exact resolve b6e91 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e91
        have b6e272 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e60 X0
             have i₂ := b6e94
             grind)
          | exact superpose b6e94 b6e60
          | exact resolve b6e60 b6e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60 b6e94
        have b6e4762 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
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
        have b6e5070 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e4762
        have b6e9846 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e5070
             grind)
          | exact superpose b6e5070 b6e13
          | exact resolve b6e13 b6e5070
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e9865 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e9846
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e9846
          | exact resolve b6e9846 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9846
        have b6e9881 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e9865
             grind)
          | exact superpose b6e9865 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e9865
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9865
        have b6e9891 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e9881
        have b6e9901 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e9891
             have r₂ := b6e20
             grind)
          | exact resolve b6e9891 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9891
        have b6e10545 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e9901
        have b6e12144 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e5070
             have i₂ := b6e10545
             grind)
          | exact superpose b6e10545 b6e5070
          | exact resolve b6e5070 b6e10545
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5070 b6e10545
        have b6e12161 : (σ x) = (σ y) := by grind
        clear b6e12144
        have b6e12644 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e12161
             grind)
          | exact superpose b6e12161 b6e22
          | exact resolve b6e22 b6e12161
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e12161
        have b6e12672 : False := by grind
        exact b6e12672
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
          have b7e82 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
          have b7e85 : y = (M.op y y) := by grind
          clear b7e82
          have b7e89 : False := by grind
          exact b7e89
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
          have b8e1941 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e61 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e1942 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1941
               have r₂ := b8e24
               grind)
            | exact resolve b8e1941 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1941
          have b8e1943 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1942
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1942
            | exact resolve b8e1942 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1942
          have b8e1944 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1943
               grind)
            | exact superpose b8e1943 b8e20
            | exact resolve b8e20 b8e1943
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1943
          have b8e1962 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e1944
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1944
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1944 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1944
          have b8e1963 : y = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e1962
          have b8e1966 : y = (M.op y y) := by
            first
            | (have r₁ := b8e1963
               have r₂ := b8e21
               grind)
            | exact resolve b8e1963 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1963
          have b8e1969 : False := by grind
          exact b8e1969

/-- `Equation4331`: `x ◇ (y ◇ x) = z ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_y_pxx_pxy_Equation4331 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4331 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4331.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
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
      have b0e32 : ∀ X0 : G, (M.op x y) = (M.op X0 y) := by
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
      have b0e39 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X0)) = (M.op X1 (σ y)) := by
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
      have b0e44 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e32 X1
           have i₂ := b0e32 X0
           grind)
        | (have i₁ := b0e32 X0
           have i₂ := b0e32 x
           grind)
        | exact superpose b0e32 b0e32
        | exact resolve b0e32 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X0 X1 : G, (M.op X1 (M.op x x)) = (M.op y (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 y x X1
           have i₂ := b0e32 X0
           grind)
        | (have i₁ := b0e11 y X0 x
           have i₂ := b0e32 X0
           grind)
        | exact superpose b0e32 b0e11
        | exact resolve b0e11 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e49 : ∀ X0 X1 : G, (M.op X1 y) = (M.op y (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e45 X0 X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e45
        | exact resolve b0e45 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
      have b0e167 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op X0 y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 y X1 X2
           have i₂ := b0e49 X1 X0
           grind)
        | exact superpose b0e49 b0e11
        | exact resolve b0e11 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e286 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e49 (σ x) X1
           have i₂ := b0e39 y X0
           grind)
        | exact superpose b0e39 b0e49
        | exact resolve b0e49 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e49
      have b0e325 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e286 (σ x) X0
           grind)
        | exact superpose b0e286 b0e18
        | exact resolve b0e18 b0e286
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e286
      have b0e442 : ∀ X0 X1 : G, (M.op X1 y) ≠ (σ (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e325 X1
           have i₂ := b0e44 x X0
           grind)
        | (have i₁ := b0e325 X1
           have i₂ := b0e44 X0 x
           grind)
        | exact superpose b0e44 b0e325
        | exact resolve b0e325 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e325
      have b0e1267 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op X1 (M.op X0 y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e167 X2 y X1
           have i₂ := b0e44 y X0
           grind)
        | (have i₁ := b0e167 X2 y X1
           have i₂ := b0e44 X0 y
           grind)
        | exact superpose b0e44 b0e167
        | exact resolve b0e167 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e1343 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) ≠ (σ (M.op X3 y)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e442 X3 x
           have i₂ := b0e167 x X1 X0
           grind)
        | exact superpose b0e167 b0e442
        | exact resolve b0e442 b0e167
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e167 b0e442
      have b0e1951 : ∀ X0 X1 : G, (M.op X0 y) = (k (M.op X1 y) (M.op X0 y)) := by
        intro X0 X1
        grind
      clear b0e1267
      have b0e5536 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e95 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e95
      have b0e5537 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e5536 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5536
      have b0e79455 : ∀ X0 : G, (σ (M.op X0 y)) ≠ (σ (M.op X0 y)) ∨ (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b0e5537 (M.op X0 y)
           have i₂ := b0e1951 X0 X0
           grind)
        | exact superpose b0e1951 b0e5537
        | (have j0 := b0e5537 (M.op X0 y)
           grind)
        | exact resolve b0e5537 b0e1951
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1951 b0e5537
      have b0e79465 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) := by
        intro X0
        first
        | (have j0 := b0e79455 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79455
      have b0e560576 : ∀ X0 X1 X2 : G, (σ (M.op X2 y)) ≠ (M.op X1 (σ (M.op X0 y))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1343 X1 (σ (M.op X0 y)) X2
           have i₂ := b0e79465 X0
           grind)
        | exact superpose b0e79465 b0e1343
        | exact resolve b0e1343 b0e79465
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1343
      have b0e560609 : ∀ X0 X1 : G, (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) = (M.op X1 (σ (M.op X0 y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ (M.op X0 y)) (σ (M.op X0 y)) x
           have i₂ := b0e79465 X0
           grind)
        | exact superpose b0e79465 b0e11
        | exact resolve b0e11 b0e79465
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e560697 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (M.op X1 (σ (M.op X0 y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e560609 X0 X1
           have i₂ := b0e79465 X0
           grind)
        | exact superpose b0e79465 b0e560609
        | exact resolve b0e560609 b0e79465
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79465 b0e560609
      have b0e560738 : False := by
        have f560738_10 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (M.op X1 (σ (M.op X0 y))) := by
          intro X0 X1
          grind
        have f560738_11 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 y))) ≠ (σ (M.op X2 y)) := by
          intro X0 X1 X2
          grind
        have f560738_20 : False := by
          first
          | (have r₁ := f560738_10 x x
             have r₂ := f560738_11 x x x
             grind)
          | exact resolve f560738_10 f560738_11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        exact f560738_20
      exact b0e560738
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
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
        have b1e35 : ∀ X0 : G, (M.op x y) = (M.op X0 y) := by
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
        have b1e36 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
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
        have b1e41 : ∀ X0 X1 : G, (M.op X0 (M.op x X0)) = (M.op X1 y) := by
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
        have b1e47 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e36 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e36
          | exact resolve b1e36 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e60 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (σ y) X0 X1
             have i₂ := b1e47 X0
             grind)
          | exact superpose b1e47 b1e12
          | exact resolve b1e12 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e62 : ∀ X0 X1 : G, (σ y) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e60 X0 X1
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e60
          | exact resolve b1e60 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e90 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
        have b1e93 : y = (M.op y y) := by grind
        clear b1e90
        have b1e114 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X2 (M.op x x)) := by
          intro X0 X2
          first
          | (have i₁ := b1e12 x x X2
             have i₂ := b1e41 x X0
             grind)
          | exact superpose b1e41 b1e12
          | exact resolve b1e12 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e121 : ∀ X0 : G, (σ y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e114 X0 x
             have i₂ := b1e62 x x
             grind)
          | exact superpose b1e62 b1e114
          | exact resolve b1e114 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62 b1e114
        have b1e139 : y = (σ y) := by
          first
          | (have i₁ := b1e93
             have i₂ := b1e121 y
             grind)
          | exact superpose b1e121 b1e93
          | exact resolve b1e93 b1e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e93
        have b1e154 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e139
             grind)
          | exact superpose b1e139 b1e19
          | exact resolve b1e19 b1e139
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e159 : (M.op x y) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e154
             have i₂ := b1e35 (σ x)
             grind)
          | exact superpose b1e35 b1e154
          | exact resolve b1e154 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35 b1e154
        have b1e160 : (σ y) ≠ (σ (σ y)) := by
          first
          | (have i₁ := b1e159
             have i₂ := b1e121 x
             grind)
          | exact superpose b1e121 b1e159
          | exact resolve b1e159 b1e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e121 b1e159
        have b1e161 : y ≠ (σ y) := by
          first
          | (have i₁ := b1e160
             have i₂ := b1e139
             grind)
          | exact superpose b1e139 b1e160
          | exact resolve b1e160 b1e139
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e160
        have b1e162 : False := by grind
        exact b1e162
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
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
        have b2e24 : y = (k x y) := by grind
        have b2e70 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
        have b2e85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b2e1951 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e70 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e1952 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1951
             have r₂ := b2e22
             grind)
          | exact resolve b2e1951 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1951
        have b2e1953 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1952
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1952
          | exact resolve b2e1952 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1952
        have b2e1954 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1953
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1953
          | exact resolve b2e1953 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1953
        have b2e5117 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e85 x x
             grind)
          | exact superpose b2e85 b2e21
          | (have j1 := b2e85 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e85 x y
             grind)
          | exact resolve b2e21 b2e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e85
        have b2e5315 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e5117
        have b2e48513 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e5315
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e5315
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e5315 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5315
        have b2e48523 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e48513
        have b2e48538 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e48523
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e48523
          | exact resolve b2e48523 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48523
        have b2e48539 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e48538
        have b2e48551 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e48539
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e48539
          | exact resolve b2e48539 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48539
        have b2e48570 : (σ x) ≠ (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e48551
             grind)
          | exact superpose b2e48551 b2e21
          | exact resolve b2e21 b2e48551
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e48575 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by grind
        clear b2e48551
        have b2e48702 : (σ x) = (σ (k x x)) ∨ x = y := by
          first
          | (have i₁ := b2e48575
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e48575
          | exact resolve b2e48575 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48575
        have b2e50018 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e48702
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e48702
          | (have j1 := b2e17 x x
             grind)
          | exact resolve b2e48702 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48702
        have b2e50049 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) := by grind
        clear b2e50018
        have b2e50073 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e50049
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e50049
          | exact resolve b2e50049 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50049
        have b2e50083 : x = y ∨ x = (M.op x x) := by
          first
          | (have r₁ := b2e50073
             have r₂ := b2e48570
             grind)
          | exact resolve b2e50073 b2e48570
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48570 b2e50073
        have b2e50095 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e50083
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e50083
          | exact resolve b2e50083 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50083
        have b2e50096 : x = y := by grind
        clear b2e50095
        have b2e52325 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e1954
             have i₂ := b2e50096
             grind)
          | exact superpose b2e50096 b2e1954
          | exact resolve b2e1954 b2e50096
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1954 b2e50096
        have b2e52330 : False := by grind
        exact b2e52330
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : (σ y) = (k (σ x) (σ y)) := by grind
        have b3e26 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b3e25
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e25
          | exact resolve b3e25 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e31 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e26
             grind)
          | exact superpose b3e26 b3e13
          | exact resolve b3e13 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e32 : y = (k x y) := by
          first
          | (have i₁ := b3e31
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e31
          | exact resolve b3e31 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e35 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
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
        have b3e47 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e35 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e35
          | exact resolve b3e35 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e55 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b3e56 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ (M.op X0 X0) = y := by
          intro X0
          first
          | (have j0 := b3e55 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e1354 : y = (M.op x x) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b3e32
             have i₂ := b3e56 x
             grind)
          | exact superpose b3e56 b3e32
          | (have j1 := b3e56 x
             grind)
          | exact resolve b3e32 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32 b3e56
        have b3e1359 : y = (M.op x x) := by grind
        clear b3e1354
        have b3e1365 : False := by grind
        exact b3e1365
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e36 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
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
          have b4e37 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
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
          have b4e48 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e37 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e37
            | exact resolve b4e37 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e49 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e36 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e36
            | exact resolve b4e36 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e65 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e48 (σ x)
               grind)
            | exact superpose b4e48 b4e20
            | exact resolve b4e20 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e67 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e65
               have i₂ := b4e49 x
               grind)
            | exact superpose b4e49 b4e65
            | exact resolve b4e65 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49 b4e65
          have b4e68 : False := by grind
          exact b4e68
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : y = (k y y) := by grind
          have b5e96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
          have b5e4059 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e96 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e96
          have b5e4060 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e4059 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4059
          have b5e5911 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e4060 y
               have i₂ := b5e26
               grind)
            | exact superpose b5e26 b5e4060
            | (have j0 := b5e4060 y
               grind)
            | exact resolve b5e4060 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e4060
          have b5e5915 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e5911
          have b5e5921 : False := by grind
          exact b5e5921
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
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
        have b6e24 : (σ y) = (k (σ x) (σ y)) := by grind
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
        have b6e39 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) := by
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
        have b6e60 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e19
             have i₂ := b6e39 X0
             grind)
          | (have i₁ := b6e19
             have i₂ := b6e39 (σ x)
             grind)
          | exact superpose b6e39 b6e19
          | exact resolve b6e19 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
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
        have b6e89 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
        have b6e91 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
          first
          | (have r₁ := b6e89
             have r₂ := b6e20
             grind)
          | exact resolve b6e89 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e89
        have b6e94 : (σ (M.op x y)) = (σ y) := by
          first
          | (have r₁ := b6e91
             have r₂ := b6e21
             grind)
          | exact resolve b6e91 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e91
        have b6e272 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e60 X0
             have i₂ := b6e94
             grind)
          | exact superpose b6e94 b6e60
          | exact resolve b6e60 b6e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60 b6e94
        have b6e4762 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
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
        have b6e5070 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e4762
        have b6e9846 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e5070
             grind)
          | exact superpose b6e5070 b6e13
          | exact resolve b6e13 b6e5070
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e9865 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e9846
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e9846
          | exact resolve b6e9846 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9846
        have b6e9881 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e9865
             grind)
          | exact superpose b6e9865 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e9865
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9865
        have b6e9891 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e9881
        have b6e9901 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e9891
             have r₂ := b6e20
             grind)
          | exact resolve b6e9891 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9891
        have b6e10545 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e9901
        have b6e12144 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e5070
             have i₂ := b6e10545
             grind)
          | exact superpose b6e10545 b6e5070
          | exact resolve b6e5070 b6e10545
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5070 b6e10545
        have b6e12161 : (σ x) = (σ y) := by grind
        clear b6e12144
        have b6e12644 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e12161
             grind)
          | exact superpose b6e12161 b6e22
          | exact resolve b6e22 b6e12161
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e12161
        have b6e12672 : False := by grind
        exact b6e12672
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
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
          have b7e82 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
          have b7e85 : y = (M.op y y) := by grind
          clear b7e82
          have b7e89 : False := by grind
          exact b7e89
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
          have b8e1941 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e61 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e1942 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1941
               have r₂ := b8e24
               grind)
            | exact resolve b8e1941 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1941
          have b8e1943 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1942
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1942
            | exact resolve b8e1942 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1942
          have b8e1944 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1943
               grind)
            | exact superpose b8e1943 b8e20
            | exact resolve b8e20 b8e1943
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1943
          have b8e1962 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e1944
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1944
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1944 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1944
          have b8e1963 : y = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e1962
          have b8e1966 : y = (M.op y y) := by
            first
            | (have r₁ := b8e1963
               have r₂ := b8e21
               grind)
            | exact resolve b8e1963 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1963
          have b8e1969 : False := by grind
          exact b8e1969

/-- `Equation4331`: `x ◇ (y ◇ x) = z ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation4331 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4331 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4331.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e28 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e11 y y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e29 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ y) (σ y) x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e29 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e29
        | exact resolve b0e29 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e40 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e28 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e28
        | exact resolve b0e28 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e51 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e39 (σ x)
           grind)
        | exact superpose b0e39 b0e18
        | exact resolve b0e18 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e57 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e51
           have i₂ := b0e40 x
           grind)
        | exact superpose b0e40 b0e51
        | exact resolve b0e51 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e51
      have b0e58 : False := by grind
      exact b0e58
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e12 y y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e26 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e26
          | exact resolve b1e26 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e39 : ∀ X0 X1 : G, (M.op y y) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 y X0 X1
             have i₂ := b1e37 X0
             grind)
          | exact superpose b1e37 b1e12
          | exact resolve b1e12 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : ∀ X0 X1 : G, y = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e39 X0 X1
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e39
          | exact resolve b1e39 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e44 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 y
             have i₂ := b1e37 y
             grind)
          | exact superpose b1e37 b1e15
          | (have j0 := b1e15 X0 y
             grind)
          | (have r₁ := b1e15 X0 y
             have r₂ := b1e37 y
             grind)
          | exact resolve b1e15 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e44 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e48 : ∀ X0 : G, y = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e40 (σ x) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e40
          | exact resolve b1e40 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e72 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e21
             have i₂ := b1e17 X0 (σ y)
             grind)
          | exact superpose b1e17 b1e21
          | (have j1 := b1e17 X0 (σ y)
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e17 X0 (σ y)
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e17 (σ y) (σ y)
             grind)
          | exact resolve b1e21 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e90 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e72 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72
        have b1e97 : ∀ X0 : G, y = (k X0 (σ y)) ∨ (M.op X0 X0) = (σ y) := by
          intro X0
          first
          | (have i₁ := b1e90 X0
             have i₂ := b1e48 X0
             grind)
          | exact superpose b1e48 b1e90
          | (have j0 := b1e90 X0
             grind)
          | exact resolve b1e90 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e90
        have b1e108 : y ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e48 (σ y)
             grind)
          | exact superpose b1e48 b1e21
          | exact resolve b1e21 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e763 : ∀ X0 : G, y = (σ y) ∨ y = (k (M.op X0 X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e40 X0 (M.op X0 X0)
             have i₂ := b1e97 (M.op X0 X0)
             grind)
          | exact superpose b1e97 b1e40
          | (have j1 := b1e97 (M.op X0 X0)
             grind)
          | exact resolve b1e40 b1e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40 b1e97
        have b1e771 : ∀ X0 : G, y = (k (M.op X0 X0) (σ y)) := by
          intro X0
          first
          | (have j0 := b1e763 X0
             grind)
          | (have r₁ := b1e763 X0
             have r₂ := b1e108
             grind)
          | exact resolve b1e763 b1e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e763
        have b1e800 : y = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e771 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e771
          | exact resolve b1e771 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e771
        have b1e803 : y = (σ (k y y)) := by
          first
          | (have i₁ := b1e800
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e800
          | exact resolve b1e800 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e800
        have b1e808 : y = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e803
             have i₂ := b1e45 y
             grind)
          | exact superpose b1e45 b1e803
          | exact resolve b1e803 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45 b1e803
        have b1e810 : y = (σ y) := by
          first
          | (have i₁ := b1e808
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e808
          | exact resolve b1e808 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e808
        have b1e812 : False := by grind
        exact b1e812
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
        have b2e26 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e12 y y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e26 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e26
          | exact resolve b2e26 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e41 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b2e15 X0 y
             have i₂ := b2e35 y
             grind)
          | exact superpose b2e35 b2e15
          | (have j0 := b2e15 X0 y
             grind)
          | (have r₁ := b2e15 X0 y
             have r₂ := b2e35 y
             grind)
          | exact resolve b2e15 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e42 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b2e41 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b2e85 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) y) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e82 X0 X1
             have i₂ := b2e42 (σ X1)
             grind)
          | exact superpose b2e42 b2e82
          | (have j0 := b2e82 X0 X1
             grind)
          | exact resolve b2e82 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) y) ∨ (σ X1) = (k (σ X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b2e85 X0 X1
             have i₂ := b2e42 (σ X0)
             grind)
          | exact superpose b2e42 b2e85
          | (have j0 := b2e85 X0 X1
             grind)
          | exact resolve b2e85 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e85
        have b2e104 : (σ y) ≠ (k (σ y) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e42 (σ y)
             grind)
          | exact superpose b2e42 b2e21
          | exact resolve b2e21 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3634 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e95 y y
             grind)
          | exact superpose b2e95 b2e21
          | (have j1 := b2e95 y y
             grind)
          | exact resolve b2e21 b2e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e95
        have b2e3704 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) := by grind
        clear b2e3634
        have b2e3741 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b2e3704
             have r₂ := b2e104
             grind)
          | exact resolve b2e3704 b2e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e104 b2e3704
        have b2e3759 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e3741
             have i₂ := b2e42 y
             grind)
          | exact superpose b2e42 b2e3741
          | exact resolve b2e3741 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42 b2e3741
        have b2e3763 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e3759
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e3759
          | exact resolve b2e3759 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3759
        have b2e3764 : False := by grind
        exact b2e3764
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) (σ y) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : ∀ X0 X1 : G, (M.op X0 (M.op x X0)) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 x X1
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e37 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e27 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e27
          | exact resolve b3e27 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e44 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X1 X1) ∨ (M.op X2 X2) = (k X2 (M.op X1 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e15 X2 (M.op X1 X1)
             have i₂ := b3e12 X0 X1 (M.op X1 X1)
             grind)
          | exact superpose b3e12 b3e15
          | (have j0 := b3e15 X2 (M.op X1 X1)
             grind)
          | exact resolve b3e15 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e48 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (σ y) X0 X1
             have i₂ := b3e37 X0
             grind)
          | exact superpose b3e37 b3e12
          | exact resolve b3e12 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e49 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e37 (σ x)
             grind)
          | exact superpose b3e37 b3e19
          | exact resolve b3e19 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e51 : ∀ X0 X1 : G, (σ y) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e48 X0 X1
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e48
          | exact resolve b3e48 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e107 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0 X1
          grind
        have b3e116 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b3e107 X0 x
             have j1 := b3e44 X0 X0 X0
             grind)
          | (have r₁ := b3e107 x X0
             have r₂ := b3e44 X0 x x
             grind)
          | exact resolve b3e107 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44 b3e107
        have b3e161 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X2 (M.op x x)) := by
          intro X0 X2
          first
          | (have i₁ := b3e12 x x X2
             have i₂ := b3e32 x X0
             grind)
          | exact superpose b3e32 b3e12
          | exact resolve b3e12 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e171 : ∀ X0 : G, (σ y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e161 X0 x
             have i₂ := b3e51 x x
             grind)
          | exact superpose b3e51 b3e161
          | exact resolve b3e161 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51 b3e161
        have b3e206 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e116 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e116
          | exact resolve b3e116 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e116
        have b3e208 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e206
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e206
          | exact resolve b3e206 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e206
        have b3e223 : (σ y) ≠ (σ (σ y)) := by
          first
          | (have i₁ := b3e49
             have i₂ := b3e171 x
             grind)
          | exact superpose b3e171 b3e49
          | exact resolve b3e49 b3e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e238 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e208
             have i₂ := b3e17 y y
             grind)
          | exact superpose b3e17 b3e208
          | (have j1 := b3e17 y y
             grind)
          | exact resolve b3e208 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e208
        have b3e242 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b3e238
        have b3e246 : (σ y) = (σ (M.op y y)) := by
          first
          | (have r₁ := b3e242
             have r₂ := b3e20
             grind)
          | exact resolve b3e242 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e242
        have b3e247 : (σ y) = (σ (σ y)) := by
          first
          | (have i₁ := b3e246
             have i₂ := b3e171 y
             grind)
          | exact superpose b3e171 b3e246
          | exact resolve b3e246 b3e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e171 b3e246
        have b3e248 : False := by grind
        exact b3e248
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
            intro X0 X1 X2
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y y) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e32 : ∀ X0 : G, (M.op x y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e13 x x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) (σ x) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op (M.op X1 X2) (M.op X0 (M.op X1 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X1 X2) X2 X3
               have i₂ := b4e13 X2 X1 X0
               grind)
            | (have i₁ := b4e13 (M.op X1 X1) X2 X2
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X1 X1) X2 X3
               have i₂ := b4e13 X0 X1 X2
               grind)
            | (have i₁ := b4e13 (M.op X1 X0) X0 X2
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 : G, (M.op X0 (M.op x X0)) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 x X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X0)) = (M.op X1 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (σ x) X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X1) X2)) = (M.op X3 (M.op X0 (M.op X1 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 (M.op X1 X1) X3
               have i₂ := b4e13 X0 X1 (M.op X1 X1)
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X1 x
               have i₂ := b4e13 X2 X1 x
               grind)
            | (have i₁ := b4e13 X0 X0 X0
               have i₂ := b4e13 X0 X0 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X1
               have i₂ := b4e32 X0
               grind)
            | (have i₁ := b4e32 X0
               have i₂ := b4e32 x
               grind)
            | exact superpose b4e32 b4e32
            | exact resolve b4e32 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 X1 : G, (M.op X1 (M.op x x)) = (M.op y (M.op X0 y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 y x X1
               have i₂ := b4e32 X0
               grind)
            | (have i₁ := b4e13 y X0 x
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e13
            | exact resolve b4e13 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46 : ∀ X0 X1 : G, (M.op X1 y) = (M.op y (M.op X0 y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e44 X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e44
            | exact resolve b4e44 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e69 : ∀ X0 : G, y ≠ (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e21
               have i₂ := b4e43 y X0
               grind)
            | (have i₁ := b4e21
               have i₂ := b4e43 X0 y
               grind)
            | exact superpose b4e43 b4e21
            | exact resolve b4e21 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e81 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X2 X2) ∨ (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X0 (M.op X0 X0)
               have i₂ := b4e18 X2 (M.op X0 X0)
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X0 (M.op X1 (M.op X0 X1))
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e82 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e23
               have i₂ := b4e18 X0 (σ y)
               grind)
            | exact superpose b4e18 b4e23
            | (have j1 := b4e18 X0 (σ y)
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e18 X0 (σ y)
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e18 (σ y) (σ y)
               grind)
            | exact resolve b4e23 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e92 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b4e82 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e82
          have b4e141 : ∀ X0 : G, y ≠ (M.op X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e69 x
               have i₂ := b4e38 X0 x
               grind)
            | exact superpose b4e38 b4e69
            | exact resolve b4e69 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e155 : ∀ X0 : G, y ≠ (M.op y (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e141 y
               have i₂ := b4e43 x X0
               grind)
            | (have i₁ := b4e141 y
               have i₂ := b4e43 X0 x
               grind)
            | exact superpose b4e43 b4e141
            | exact resolve b4e141 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e176 : ∀ X0 X1 : G, y ≠ (M.op X0 (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e155 X1
               have i₂ := b4e13 y X1 X0
               grind)
            | (have i₁ := b4e155 y
               have i₂ := b4e13 X0 y y
               grind)
            | exact superpose b4e13 b4e155
            | exact resolve b4e155 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e155
          have b4e314 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op y (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b4e39 y X0
               have i₂ := b4e32 (σ x)
               grind)
            | exact superpose b4e32 b4e39
            | exact resolve b4e39 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e511 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op X0 y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 y X1 X2
               have i₂ := b4e46 X1 X0
               grind)
            | exact superpose b4e46 b4e13
            | exact resolve b4e13 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e516 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e39 y X1
               have i₂ := b4e46 (σ x) X0
               grind)
            | exact superpose b4e46 b4e39
            | exact resolve b4e39 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e46
          have b4e565 : ∀ X0 : G, (σ y) ≠ (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e23
               have i₂ := b4e516 X0 (σ y)
               grind)
            | exact superpose b4e516 b4e23
            | exact resolve b4e23 b4e516
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e567 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e20
               have i₂ := b4e516 X0 (σ x)
               grind)
            | exact superpose b4e516 b4e20
            | exact resolve b4e20 b4e516
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e516
          have b4e690 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X2 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e42 (M.op X1 X1) X2 X3
               have i₂ := b4e34 X2 X1 X1 X0
               grind)
            | (have i₁ := b4e42 X2 X2 X2
               have i₂ := b4e34 X0 X1 X2 X2
               grind)
            | exact superpose b4e34 b4e42
            | exact resolve b4e42 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e42
          have b4e756 : ∀ X0 : G, (σ y) ≠ (M.op X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e565 x
               have i₂ := b4e38 X0 x
               grind)
            | exact superpose b4e38 b4e565
            | exact resolve b4e565 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38 b4e565
          have b4e985 : ∀ X0 X1 X2 : G, (M.op y (M.op x y)) = (M.op X1 (M.op X2 (M.op X0 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e40 X2 X0 y X1
               have i₂ := b4e32 (M.op X0 X0)
               grind)
            | exact superpose b4e32 b4e40
            | exact resolve b4e40 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e1254 : ∀ X0 X1 : G, (M.op X1 y) ≠ (σ (M.op X0 y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e567 X1
               have i₂ := b4e43 x X0
               grind)
            | (have i₁ := b4e567 X1
               have i₂ := b4e43 X0 x
               grind)
            | exact superpose b4e43 b4e567
            | exact resolve b4e567 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43 b4e567
          have b4e1296 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op X1 X1) (M.op X2 (M.op X1 X2))) ∨ (M.op (M.op X0 X0) (σ y)) = (k (M.op X0 X0) (σ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e35 X2 X1 X0 (M.op X0 X0)
               have i₂ := b4e92 (M.op X0 X0)
               grind)
            | exact superpose b4e92 b4e35
            | (have j1 := b4e92 (M.op X0 X0)
               grind)
            | exact resolve b4e35 b4e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35 b4e92
          have b4e1316 : ∀ X0 : G, (σ y) = (M.op y (M.op x y)) ∨ (M.op (M.op X0 X0) (σ y)) = (k (M.op X0 X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e1296 X0 x x
               have i₂ := b4e985 x (M.op x x) x
               grind)
            | exact superpose b4e985 b4e1296
            | (have j0 := b4e1296 X0 x x
               grind)
            | exact resolve b4e1296 b4e985
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e985 b4e1296
          have b4e1340 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (k (M.op X0 X0) (σ y)) := by
            intro X0
            first
            | (have j0 := b4e1316 X0
               grind)
            | (have r₁ := b4e1316 X0
               have r₂ := b4e756 y
               grind)
            | exact resolve b4e1316 b4e756
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e756 b4e1316
          have b4e1352 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op X0 X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e1340 X0
               have i₂ := b4e33 (M.op X0 X0)
               grind)
            | exact superpose b4e33 b4e1340
            | exact resolve b4e1340 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e1340
          have b4e1360 : ∀ X0 : G, (M.op y (M.op x y)) = (k (M.op X0 X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e1352 X0
               have i₂ := b4e314 (σ x)
               grind)
            | exact superpose b4e314 b4e1352
            | exact resolve b4e1352 b4e314
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e314 b4e1352
          have b4e5412 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) ≠ (σ (M.op X3 y)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e1254 X3 x
               have i₂ := b4e511 x X1 X0
               grind)
            | exact superpose b4e511 b4e1254
            | exact resolve b4e1254 b4e511
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e511 b4e1254
          have b4e7496 : ∀ X0 X1 : G, (M.op X0 y) = (k X0 y) ∨ y = (M.op X1 (M.op x X1)) ∨ (M.op X0 X0) = y := by
            intro X0 X1
            first
            | (have i₁ := b4e81 x X1 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e81
            | exact resolve b4e81 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81
          have b4e7914 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (M.op X0 X0) = y := by
            intro X0
            first
            | (have j0 := b4e7496 X0 x
               grind)
            | (have r₁ := b4e7496 X0 X0
               have r₂ := b4e141 X0
               grind)
            | exact resolve b4e7496 b4e141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e141 b4e7496
          have b4e15285 : (M.op y (M.op x y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e1360 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e1360
            | exact resolve b4e1360 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1360
          have b4e15313 : (M.op y (M.op x y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e15285
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e15285
            | exact resolve b4e15285 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15285
          have b4e16163 : ∀ X0 : G, y ≠ y ∨ (M.op (M.op X0 X0) y) = (k (M.op X0 X0) y) := by
            intro X0
            first
            | (have i₁ := b4e176 (M.op X0 X0) X0
               have i₂ := b4e7914 (M.op X0 X0)
               grind)
            | exact superpose b4e7914 b4e176
            | (have j1 := b4e7914 (M.op X0 X0)
               grind)
            | (have r₁ := b4e176 (M.op x x) x
               have r₂ := b4e7914 (M.op x x)
               grind)
            | exact resolve b4e176 b4e7914
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e176 b4e7914
          have b4e16222 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (k (M.op X0 X0) y) := by
            intro X0
            first
            | (have j0 := b4e16163 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16163
          have b4e16259 : ∀ X0 : G, (M.op x y) = (k (M.op X0 X0) y) := by
            intro X0
            first
            | (have i₁ := b4e16222 X0
               have i₂ := b4e32 (M.op X0 X0)
               grind)
            | exact superpose b4e32 b4e16222
            | exact resolve b4e16222 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32 b4e16222
          have b4e21235 : (M.op x y) = (k y y) := by
            first
            | (have i₁ := b4e16259 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e16259
            | exact resolve b4e16259 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16259
          have b4e25532 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (σ (k y y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e690 X0 X1 x y
               have i₂ := b4e15313
               grind)
            | exact superpose b4e15313 b4e690
            | exact resolve b4e690 b4e15313
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e690 b4e15313
          have b4e25591 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e25532 X0 X1
               have i₂ := b4e21235
               grind)
            | exact superpose b4e21235 b4e25532
            | exact resolve b4e25532 b4e21235
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21235 b4e25532
          have b4e25670 : False := by grind
          exact b4e25670
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
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
          have b5e79 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X2 X2) = (k X2 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 X2 X1
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e16 X0 X1
               have i₂ := b5e18 X0 (M.op X1 X1)
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X2 X1
               have j1 := b5e18 X0 X0
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X1 X1
               grind)
            | (have r₁ := b5e16 X0 (M.op X0 X0)
               have r₂ := b5e18 X0 (M.op (M.op X0 X0) (M.op X0 X0))
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e84 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
          have b5e85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e18 (σ X0) (σ X1)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X1) (σ X1)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e93 : y = (M.op y y) ∨ y = (k x y) := by grind
          have b5e113 : y = (k x y) := by
            first
            | (have r₁ := b5e93
               have r₂ := b5e21
               grind)
            | exact resolve b5e93 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e93
          have b5e1799 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e84 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84
          have b5e1800 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1799
               have r₂ := b5e23
               grind)
            | exact resolve b5e1799 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1799
          have b5e1801 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1800
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1800
            | exact resolve b5e1800 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1800
          have b5e1802 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1801
               have i₂ := b5e113
               grind)
            | exact superpose b5e113 b5e1801
            | exact resolve b5e1801 b5e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e113 b5e1801
          have b5e4095 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e79 X1 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79
          have b5e4096 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e4095 X0 X1
               have j1 := b5e16 X0 X1
               grind)
            | (have r₁ := b5e4095 X0 X1
               have r₂ := b5e16 X0 X1
               grind)
            | exact resolve b5e4095 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4095
          have b5e5521 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e85 x x
               grind)
            | exact superpose b5e85 b5e24
            | (have j1 := b5e85 x x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e85 x y
               grind)
            | exact resolve b5e24 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e5738 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e5521
          have b5e24625 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e4096 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4096
          have b5e24626 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e24625 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24625
          have b5e24651 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e24626 (σ X0)
               grind)
            | exact superpose b5e24626 b5e19
            | exact resolve b5e19 b5e24626
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e24667 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e24651 X0
               have i₂ := b5e24626 X0
               grind)
            | exact superpose b5e24626 b5e24651
            | exact resolve b5e24651 b5e24626
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24651
          have b5e48463 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e5738
               have i₂ := b5e24626 x
               grind)
            | exact superpose b5e24626 b5e5738
            | exact resolve b5e5738 b5e24626
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5738 b5e24626
          have b5e48493 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e48463
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e48463
            | exact resolve b5e48463 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48463
          have b5e48494 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e48493
          have b5e48510 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e48494
               have i₂ := b5e24667 x
               grind)
            | exact superpose b5e24667 b5e48494
            | exact resolve b5e48494 b5e24667
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24667 b5e48494
          have b5e48523 : (σ x) = (σ y) := by
            first
            | (have i₁ := b5e48510
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e48510
            | exact resolve b5e48510 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48510
          have b5e48536 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e1802
               have i₂ := b5e48523
               grind)
            | exact superpose b5e48523 b5e1802
            | exact resolve b5e1802 b5e48523
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1802 b5e48523
          have b5e48577 : False := by grind
          exact b5e48577
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
        have b6e26 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ y) (σ y) x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e35 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e26 X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e26
          | exact resolve b6e26 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e41 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X1 X1) ∨ (M.op X2 X2) = (k X2 (M.op X1 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 X2 (M.op X1 X1)
             have i₂ := b6e12 X0 X1 (M.op X1 X1)
             grind)
          | exact superpose b6e12 b6e15
          | (have j0 := b6e15 X2 (M.op X1 X1)
             grind)
          | exact resolve b6e15 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e100 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0 X1
          grind
        have b6e110 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b6e100 X0 x
             have j1 := b6e41 X0 X0 X0
             grind)
          | (have r₁ := b6e100 x X0
             have r₂ := b6e41 X0 x x
             grind)
          | exact resolve b6e100 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41 b6e100
        have b6e145 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e110 (σ y)
             have i₂ := b6e35 (σ y)
             grind)
          | exact superpose b6e35 b6e110
          | exact resolve b6e110 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35 b6e110
        have b6e150 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e145
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e145
          | exact resolve b6e145 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e145
        have b6e156 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e150
             grind)
          | exact superpose b6e150 b6e13
          | exact resolve b6e13 b6e150
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e150
        have b6e158 : y = (k y y) := by
          first
          | (have i₁ := b6e156
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e156
          | exact resolve b6e156 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e156
        have b6e170 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e158
             grind)
          | exact superpose b6e158 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e158
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e158
        have b6e171 : y = (M.op y y) := by grind
        clear b6e170
        have b6e173 : False := by grind
        exact b6e173
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e64 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e16 X1 X0
               have i₂ := b7e18 X2 X0
               grind)
            | exact superpose b7e18 b7e16
            | (have j0 := b7e16 X1 X0
               have j1 := b7e18 X2 X0
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X1 X1
               grind)
            | (have r₁ := b7e16 X0 (M.op X0 X0)
               have r₂ := b7e18 X0 (M.op (M.op X0 X0) (M.op X0 X0))
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e66 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X2 X2) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X1 X2
               have i₂ := b7e18 X0 X1
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X2 X0
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X0 X1
               have i₂ := b7e18 (σ X0) (σ X1)
               grind)
            | exact superpose b7e18 b7e19
            | (have j1 := b7e18 (σ X1) (σ X1)
               grind)
            | exact resolve b7e19 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e80 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b7e64 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e2136 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e66 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e2137 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e2136 X0 X1
               have j1 := b7e16 X0 X0
               grind)
            | (have r₁ := b7e2136 X1 X1
               have r₂ := b7e16 X0 X1
               grind)
            | exact resolve b7e2136 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2136
          have b7e5900 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e76 x x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e76
            | exact resolve b7e76 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e6250 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
          clear b7e5900
          have b7e13316 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b7e2137 (σ x) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e2137
            | exact resolve b7e2137 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2137
          have b7e13343 : (σ y) = (σ (k x x)) ∨ (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e13316
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e13316
            | exact resolve b7e13316 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13316
          have b7e13373 : (σ y) = (σ (k x x)) := by
            first
            | (have r₁ := b7e13343
               have r₂ := b7e6250
               grind)
            | exact resolve b7e13343 b7e6250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13343
          have b7e13391 : (τ (σ y)) = (k x x) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e13373
               grind)
            | exact superpose b7e13373 b7e14
            | exact resolve b7e14 b7e13373
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13373
          have b7e13409 : y = (k x x) := by
            first
            | (have i₁ := b7e13391
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e13391
            | exact resolve b7e13391 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13391
          have b7e13434 : ∀ X0 : G, y = (M.op x x) ∨ (M.op X0 X0) = (k X0 x) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b7e80 x X0 x
               have i₂ := b7e13409
               grind)
            | exact superpose b7e13409 b7e80
            | (have j0 := b7e80 x X0 x
               grind)
            | exact resolve b7e80 b7e13409
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80 b7e13409
          have b7e13441 : ∀ X0 : G, y = (M.op x x) ∨ (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b7e13434 X0
               have j1 := b7e16 X0 x
               grind)
            | (have r₁ := b7e13434 X0
               have r₂ := b7e16 X0 x
               grind)
            | exact resolve b7e13434 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13434
          have b7e13457 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b7e13441 X0
               grind)
            | (have r₁ := b7e13441 X0
               have r₂ := b7e22
               grind)
            | exact resolve b7e13441 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13441
          have b7e13468 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e6250
               grind)
            | exact superpose b7e6250 b7e14
            | exact resolve b7e14 b7e6250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6250
          have b7e13486 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e13468
               have i₂ := b7e13457 x
               grind)
            | exact superpose b7e13457 b7e13468
            | exact resolve b7e13468 b7e13457
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13457 b7e13468
          have b7e13489 : y = (M.op x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e13486
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e13486
            | exact resolve b7e13486 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13486
          have b7e13492 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e13489
               have r₂ := b7e22
               grind)
            | exact resolve b7e13489 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13489
          have b7e13494 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e13492
               grind)
            | exact superpose b7e13492 b7e24
            | exact resolve b7e24 b7e13492
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13492
          have b7e13521 : False := by grind
          exact b7e13521
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
          have b8e73 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
          have b8e1486 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e73 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e1487 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1486
               have r₂ := b8e23
               grind)
            | exact resolve b8e1486 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1486
          have b8e1488 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1487
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1487
            | exact resolve b8e1487 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1487
          have b8e1489 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1488
               grind)
            | exact superpose b8e1488 b8e20
            | exact resolve b8e20 b8e1488
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1488
          have b8e1626 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e1489
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1489
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e1489 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1489
          have b8e1627 : y = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e1626
          have b8e1629 : y = (M.op x x) := by
            first
            | (have r₁ := b8e1627
               have r₂ := b8e21
               grind)
            | exact resolve b8e1627 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1627
          have b8e1631 : False := by grind
          exact b8e1631
