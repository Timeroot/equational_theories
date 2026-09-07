import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxx_y_pxy_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e28 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
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
      have b0e29 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ y))) := by
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
      have b0e31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 (M.op (M.op X1 X0) X1) X3
           have i₂ := b0e11 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e31 X0 X1 x X3
           have i₂ := b0e11 X0 X1 x
           grind)
        | exact superpose b0e11 b0e31
        | exact resolve b0e31 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e191 : x = (M.op x y) := by
        first
        | (have i₁ := b0e28 x
           have i₂ := b0e32 x y x
           grind)
        | exact superpose b0e32 b0e28
        | exact resolve b0e28 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e329 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e32 (σ x) (σ y) x
           have i₂ := b0e29 x
           grind)
        | exact superpose b0e29 b0e32
        | exact resolve b0e32 b0e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29 b0e32
      have b0e358 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e329
           grind)
        | exact superpose b0e329 b0e18
        | exact resolve b0e18 b0e329
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e329
      have b0e362 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e358
           have i₂ := b0e191
           grind)
        | exact superpose b0e191 b0e358
        | exact resolve b0e358 b0e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e191 b0e358
      have b0e363 : False := by grind
      exact b0e363
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
          intro X0 X1 X2
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op y y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e31 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
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
        have b1e33 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X2 (M.op (M.op X1 X0) X1) X3
             have i₂ := b1e12 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e33 X0 X1 x X3
             have i₂ := b1e12 X0 X1 x
             grind)
          | exact superpose b1e12 b1e33
          | exact resolve b1e33 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e36 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 x) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 (M.op x y) X1
             have i₂ := b1e31 (M.op (M.op x y) X0)
             grind)
          | exact superpose b1e31 b1e12
          | exact resolve b1e12 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : ∀ X1 : G, x = (M.op X1 x) := by
          intro X1
          first
          | (have i₁ := b1e36 x X1
             have i₂ := b1e31 x
             grind)
          | exact superpose b1e31 b1e36
          | exact resolve b1e36 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31 b1e36
        have b1e48 : (M.op x x) = (k x y) := by grind
        have b1e49 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op X1 (M.op (k (M.op X0 X0) X0) (M.op X0 X0))) := by
          intro X0 X1
          grind
        have b1e50 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e49 X0 x
             have i₂ := b1e34 (k (M.op X0 X0) X0) (M.op X0 X0) x
             grind)
          | exact superpose b1e34 b1e49
          | exact resolve b1e49 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e51 : x = (k x y) := by
          first
          | (have i₁ := b1e48
             have i₂ := b1e37 x
             grind)
          | exact superpose b1e37 b1e48
          | exact resolve b1e48 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e55 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have i₁ := b1e50 X0
             have i₂ := b1e34 X0 X0 (k (M.op X0 X0) X0)
             grind)
          | exact superpose b1e34 b1e50
          | exact resolve b1e50 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e50
        have b1e58 : ∀ X0 : G, (M.op X0 X0) ≠ x ∨ (M.op x x) = X0 ∨ x = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 x
             have i₂ := b1e37 X0
             grind)
          | exact superpose b1e37 b1e16
          | (have j0 := b1e16 X0 x
             grind)
          | exact resolve b1e16 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e60 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e69 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e60
        have b1e73 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e69
             have r₂ := b1e21
             grind)
          | exact resolve b1e69 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e69
        have b1e74 : ∀ X0 : G, x = X0 ∨ (M.op X0 X0) ≠ x ∨ x = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e58 X0
             have i₂ := b1e37 x
             grind)
          | exact superpose b1e37 b1e58
          | (have j0 := b1e58 X0
             grind)
          | (have r₁ := b1e58 x
             have r₂ := b1e37 x
             grind)
          | exact resolve b1e58 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e77 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e73
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e73
          | exact resolve b1e73 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e79 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e77
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e77
          | exact resolve b1e77 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e77
        have b1e80 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e79
             grind)
          | exact superpose b1e79 b1e21
          | exact resolve b1e21 b1e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e79
        have b1e94 : ∀ X0 : G, (M.op X0 X0) = x ∨ (M.op x x) = X0 ∨ x = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e37 x
             grind)
          | exact superpose b1e37 b1e17
          | (have j0 := b1e17 x X0
             grind)
          | exact resolve b1e17 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e150 : ∀ X0 : G, x = X0 ∨ (M.op X0 X0) = x ∨ x = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e94 X0
             have i₂ := b1e37 x
             grind)
          | exact superpose b1e37 b1e94
          | (have j0 := b1e94 X0
             grind)
          | exact resolve b1e94 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37 b1e94
        have b1e168 : ∀ X0 : G, x = (k X0 x) ∨ x = X0 := by
          intro X0
          first
          | (have j0 := b1e150 X0
             have j1 := b1e74 X0
             grind)
          | (have r₁ := b1e150 (M.op X0 X0)
             have r₂ := b1e74 X0
             grind)
          | (have r₁ := b1e150 X0
             have r₂ := b1e74 X0
             grind)
          | exact resolve b1e150 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74 b1e150
        have b1e265 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ (τ X0) = x := by
          intro X0
          first
          | (have i₁ := b1e25 X0 x
             have i₂ := b1e168 (τ X0)
             grind)
          | exact superpose b1e168 b1e25
          | (have j1 := b1e168 (τ X0)
             grind)
          | exact resolve b1e25 b1e168
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e168
        have b1e1024 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (τ (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b1e55 (σ x)
             have i₂ := b1e265 (M.op (σ x) (σ x))
             grind)
          | exact superpose b1e265 b1e55
          | (have j1 := b1e265 (M.op (σ x) (σ x))
             grind)
          | exact resolve b1e55 b1e265
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e265
        have b1e1030 : x = (τ (M.op (σ x) (σ x))) := by
          first
          | (have r₁ := b1e1024
             have r₂ := b1e80
             grind)
          | exact resolve b1e1024 b1e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1024
        have b1e1265 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e14 (M.op (σ x) (σ x))
             have i₂ := b1e1030
             grind)
          | exact superpose b1e1030 b1e14
          | exact resolve b1e14 b1e1030
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1030
        have b1e1266 : False := by grind
        exact b1e1266
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e30 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
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
        have b2e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X2 (M.op (M.op X1 X0) X1) X3
             have i₂ := b2e12 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e32 X0 X1 x X3
             have i₂ := b2e12 X0 X1 x
             grind)
          | exact superpose b2e12 b2e32
          | exact resolve b2e32 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e35 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 x) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 (M.op x y) X1
             have i₂ := b2e30 (M.op (M.op x y) X0)
             grind)
          | exact superpose b2e30 b2e12
          | exact resolve b2e12 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X1 : G, x = (M.op X1 x) := by
          intro X1
          first
          | (have i₁ := b2e35 x X1
             have i₂ := b2e30 x
             grind)
          | exact superpose b2e30 b2e35
          | exact resolve b2e35 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e41 : (k x y) = (M.op x x) := by grind
        have b2e51 : x = (k x y) := by
          first
          | (have i₁ := b2e41
             have i₂ := b2e36 x
             grind)
          | exact superpose b2e36 b2e41
          | exact resolve b2e41 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e41
        have b2e94 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (σ y)
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 (M.op (σ y) (σ y)) x
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e171 : x = (M.op x y) := by
          first
          | (have i₁ := b2e30 x
             have i₂ := b2e33 x y x
             grind)
          | exact superpose b2e33 b2e30
          | exact resolve b2e30 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30 b2e33
        have b2e1723 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e94 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e94
        have b2e1724 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1723
             have r₂ := b2e22
             grind)
          | exact resolve b2e1723 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1723
        have b2e1725 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1724
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1724
          | exact resolve b2e1724 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1724
        have b2e1726 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1725
             have i₂ := b2e51
             grind)
          | exact superpose b2e51 b2e1725
          | exact resolve b2e1725 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e1725
        have b2e1728 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e1726
             grind)
          | exact superpose b2e1726 b2e19
          | exact resolve b2e19 b2e1726
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1726
        have b2e1745 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e1728
             have i₂ := b2e171
             grind)
          | exact superpose b2e171 b2e1728
          | exact resolve b2e1728 b2e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e171 b2e1728
        have b2e1746 : False := by grind
        exact b2e1746
  · rcases eq_or_ne (M.op x x) (M.op x y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op y y) := by grind
        have b3e21 : (M.op x y) = (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e18
          | exact resolve b3e18 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e28 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ y))) := by
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
        have b3e30 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X2 (M.op (M.op X1 X0) X1) X3
             have i₂ := b3e12 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e30 X0 X1 x X3
             have i₂ := b3e12 X0 X1 x
             grind)
          | exact superpose b3e12 b3e30
          | exact resolve b3e30 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e38 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        have b3e39 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op X1 (M.op (k (M.op X0 X0) X0) (M.op X0 X0))) := by
          intro X0 X1
          grind
        have b3e40 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e39 X0 x
             have i₂ := b3e31 (k (M.op X0 X0) X0) (M.op X0 X0) x
             grind)
          | exact superpose b3e31 b3e39
          | exact resolve b3e39 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e41 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e38
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e38
          | exact resolve b3e38 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e43 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have i₁ := b3e40 X0
             have i₂ := b3e31 X0 X0 (k (M.op X0 X0) X0)
             grind)
          | exact superpose b3e31 b3e40
          | exact resolve b3e40 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e47 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e31 (σ y) (σ y) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e31
          | exact resolve b3e31 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e64 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op y y) ∨ y = (k x y) := by
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
        have b3e70 : x = (M.op y y) ∨ y = (k x y) := by grind
        clear b3e64
        have b3e75 : y = (k x y) := by
          first
          | (have r₁ := b3e70
             have r₂ := b3e20
             grind)
          | exact resolve b3e70 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70
        have b3e171 : ∀ X0 : G, (σ x) = X0 ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e17 X0 (σ x)
             have i₂ := b3e47 (σ x)
             grind)
          | exact superpose b3e47 b3e17
          | (have j0 := b3e17 X0 (σ x)
             grind)
          | exact resolve b3e17 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e181 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = X0 ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e171 X0
             have i₂ := b3e47 X0
             grind)
          | exact superpose b3e47 b3e171
          | (have j0 := b3e171 X0
             grind)
          | exact resolve b3e171 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e171
        have b3e188 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = X0 := by
          intro X0
          first
          | (have i₁ := b3e181 X0
             have i₂ := b3e47 X0
             grind)
          | exact superpose b3e47 b3e181
          | (have j0 := b3e181 X0
             grind)
          | exact resolve b3e181 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47 b3e181
        have b3e199 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b3e43 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e43
          | exact resolve b3e43 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e200 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b3e199
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e199
          | exact resolve b3e199 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e199
        have b3e203 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e200
             have i₂ := b3e75
             grind)
          | exact superpose b3e75 b3e200
          | exact resolve b3e200 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e200
        have b3e204 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e203
             grind)
          | exact superpose b3e203 b3e24
          | exact resolve b3e24 b3e203
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e208 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e203
             grind)
          | exact superpose b3e203 b3e13
          | exact resolve b3e13 b3e203
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e209 : x = y := by
          first
          | (have i₁ := b3e208
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e208
          | exact resolve b3e208 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e208
        have b3e212 : (σ (M.op x x)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e204
             have i₂ := b3e41
             grind)
          | exact superpose b3e41 b3e204
          | exact resolve b3e204 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e204
        have b3e213 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e212
             have i₂ := b3e75
             grind)
          | exact superpose b3e75 b3e212
          | exact resolve b3e212 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e212
        have b3e214 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e213
             have i₂ := b3e203
             grind)
          | exact superpose b3e203 b3e213
          | exact resolve b3e213 b3e203
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e213
        have b3e220 : x ≠ (M.op x x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e209
             grind)
          | exact superpose b3e209 b3e20
          | exact resolve b3e20 b3e209
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e209
        have b3e234 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k X0 (τ X1))
             have i₂ := b3e26 X1 X0
             grind)
          | exact superpose b3e26 b3e13
          | exact resolve b3e13 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e251 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = X0 ∨ (M.op (σ x) (σ y)) = (k X0 (M.op (σ x) (σ y))) := by
          intro X0
          first
          | (have i₁ := b3e16 X0 (M.op (σ x) (σ y))
             have i₂ := b3e28 X0
             grind)
          | exact superpose b3e28 b3e16
          | (have j0 := b3e16 X0 (M.op (σ x) (σ y))
             grind)
          | exact resolve b3e16 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e255 : ∀ X0 : G, (σ x) = X0 ∨ (M.op X0 X0) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k X0 (M.op (σ x) (σ y))) := by
          intro X0
          first
          | (have i₁ := b3e251 X0
             have i₂ := b3e28 (M.op (σ x) (σ y))
             grind)
          | exact superpose b3e28 b3e251
          | (have j0 := b3e251 X0
             grind)
          | (have r₁ := b3e251 (M.op (σ x) (σ y))
             have r₂ := b3e28 (M.op (σ x) (σ y))
             grind)
          | exact resolve b3e251 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e251
        have b3e271 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k X0 (M.op (σ x) (σ x))) ∨ (σ x) = X0 ∨ (M.op X0 X0) ≠ (σ x) := by
          intro X0
          first
          | (have i₁ := b3e255 X0
             have i₂ := b3e203
             grind)
          | exact superpose b3e203 b3e255
          | (have j0 := b3e255 X0
             grind)
          | exact resolve b3e255 b3e203
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e255
        have b3e282 : ∀ X0 : G, (σ (k x y)) = (k X0 (σ (k x y))) ∨ (σ x) = X0 ∨ (M.op X0 X0) ≠ (σ x) := by
          intro X0
          first
          | (have i₁ := b3e271 X0
             have i₂ := b3e41
             grind)
          | exact superpose b3e41 b3e271
          | (have j0 := b3e271 X0
             grind)
          | exact resolve b3e271 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41 b3e271
        have b3e293 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ x) = X0 ∨ (M.op X0 X0) ≠ (σ x) := by
          intro X0
          first
          | (have i₁ := b3e282 X0
             have i₂ := b3e75
             grind)
          | exact superpose b3e75 b3e282
          | (have j0 := b3e282 X0
             grind)
          | exact resolve b3e282 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75 b3e282
        have b3e303 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ (σ x) = X0 ∨ (M.op X0 X0) ≠ (σ x) := by
          intro X0
          first
          | (have i₁ := b3e293 X0
             have i₂ := b3e203
             grind)
          | exact superpose b3e203 b3e293
          | (have j0 := b3e293 X0
             grind)
          | exact resolve b3e293 b3e203
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e203 b3e293
        have b3e312 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ (σ x) = X0 := by
          intro X0
          first
          | (have j0 := b3e303 X0
             have j1 := b3e188 X0
             grind)
          | (have r₁ := b3e303 X0
             have r₂ := b3e188 X0
             grind)
          | (have r₁ := b3e303 X0
             have r₂ := b3e188 (M.op X0 X0)
             grind)
          | exact resolve b3e303 b3e188
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e188 b3e303
        have b3e1384 : ∀ X0 : G, (τ (σ x)) = (k X0 (τ (σ x))) ∨ (σ X0) = (σ x) := by
          intro X0
          first
          | (have i₁ := b3e234 X0 (σ x)
             have i₂ := b3e312 (σ X0)
             grind)
          | exact superpose b3e312 b3e234
          | (have j1 := b3e312 (σ X0)
             grind)
          | exact resolve b3e234 b3e312
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e234 b3e312
        have b3e1388 : ∀ X0 : G, x = (k X0 x) ∨ (σ X0) = (σ x) := by
          intro X0
          first
          | (have i₁ := b3e1384 X0
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e1384
          | (have j0 := b3e1384 X0
             grind)
          | exact resolve b3e1384 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1384
        have b3e1541 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e43 x
             have i₂ := b3e1388 (M.op x x)
             grind)
          | exact superpose b3e1388 b3e43
          | (have j1 := b3e1388 (M.op x x)
             grind)
          | exact resolve b3e43 b3e1388
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43 b3e1388
        have b3e1545 : (σ x) = (σ (M.op x x)) := by
          first
          | (have r₁ := b3e1541
             have r₂ := b3e220
             grind)
          | exact resolve b3e1541 b3e220
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e220 b3e1541
        have b3e1547 : False := by grind
        exact b3e1547
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op x x) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
          have b4e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 (M.op (M.op X1 X0) X1) X3
               have i₂ := b4e13 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e32 X0 X1 x X3
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e32
            | exact resolve b4e32 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e54 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b4e70 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X2) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X2 ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 X2 (M.op X0 X1)
               have i₂ := b4e33 X0 X1 X2
               grind)
            | exact superpose b4e33 b4e17
            | (have j0 := b4e17 X2 (M.op X0 X1)
               grind)
            | (have r₁ := b4e17 X1 (M.op X1 X1)
               have r₂ := b4e33 X1 X1 X1
               grind)
            | exact resolve b4e17 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e85 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X2) ∨ (M.op X0 X1) = X2 ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e70 X0 X1 X2
               have i₂ := b4e33 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b4e33 b4e70
            | (have j0 := b4e70 X0 X1 X2
               grind)
            | (have r₁ := b4e70 X0 X1 (M.op X0 X1)
               have r₂ := b4e33 X0 X1 (M.op X0 X1)
               grind)
            | (have r₁ := b4e70 x (M.op X1 X1) X1
               have r₂ := b4e33 X1 X1 x
               grind)
            | exact resolve b4e70 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e97 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X2) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X2 ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e18 x (M.op X0 X1)
               have i₂ := b4e33 X0 X1 x
               grind)
            | exact superpose b4e33 b4e18
            | (have j0 := b4e18 (M.op X0 X1) X2
               grind)
            | exact resolve b4e18 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e115 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
               have r₂ := b4e18 (M.op X1 X1) X1
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 (M.op X1 X1) X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e133 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e115 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115
          have b4e134 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e133 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e133
          have b4e149 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (M.op X0 X1) = (M.op X2 X2) ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e97 X0 X1 X2
               have i₂ := b4e33 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b4e33 b4e97
            | (have j0 := b4e97 X0 X1 X2
               grind)
            | exact resolve b4e97 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e97
          have b4e161 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X2 (M.op X0 X1)) ∨ (M.op X0 X1) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e149 X0 X1 X2
               have j1 := b4e85 X0 X1 X2
               grind)
            | (have r₁ := b4e149 X0 X1 (M.op X2 X2)
               have r₂ := b4e85 X0 X1 X2
               grind)
            | (have r₁ := b4e149 X2 X2 (M.op X0 X1)
               have r₂ := b4e85 X0 X1 X2
               grind)
            | (have r₁ := b4e149 X0 X1 X2
               have r₂ := b4e85 X0 X1 X2
               grind)
            | exact resolve b4e149 b4e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85 b4e149
          have b4e207 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e28 X0 X1
               grind)
            | exact superpose b4e28 b4e14
            | exact resolve b4e14 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28
          have b4e217 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b4e29 X0 (M.op (τ X0) (τ X0))
               have i₂ := b4e54 (τ X0)
               grind)
            | exact superpose b4e54 b4e29
            | exact resolve b4e29 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29
          have b4e242 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b4e207 (M.op (σ X0) (σ X0)) X0
               have i₂ := b4e54 (σ X0)
               grind)
            | exact superpose b4e54 b4e207
            | exact resolve b4e207 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54 b4e207
          have b4e6265 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) ∨ (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e161 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
               have i₂ := b4e217 (M.op X0 X1)
               grind)
            | exact superpose b4e217 b4e161
            | (have j0 := b4e161 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
               grind)
            | exact resolve b4e161 b4e217
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e161 b4e217
          have b4e6270 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
            intro X0 X1
            first
            | (have j0 := b4e6265 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6265
          have b4e6492 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))
               have i₂ := b4e6270 X0 X1
               grind)
            | exact superpose b4e6270 b4e14
            | exact resolve b4e14 b4e6270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e6963 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) ≠ (M.op (τ (M.op X0 X1)) X2) ∨ (M.op X2 X2) = (τ (M.op X0 X1)) ∨ (k (τ (M.op X0 X1)) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 (τ (M.op X0 X1)) X2
               have i₂ := b4e6492 X0 X1
               grind)
            | exact superpose b4e6492 b4e17
            | (have j0 := b4e17 (τ (M.op X0 X1)) X2
               grind)
            | exact resolve b4e17 b4e6492
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6492
          have b4e8762 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (τ (M.op (σ X0) (σ X0))) X0) ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e242 X0
               have i₂ := b4e134 (τ (M.op (σ X0) (σ X0))) X0
               grind)
            | exact superpose b4e134 b4e242
            | (have j1 := b4e134 (τ (M.op (σ X0) (σ X0))) X0
               grind)
            | exact resolve b4e242 b4e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e134
          have b4e8802 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e8762 X0
               have j1 := b4e6963 (σ X0) (σ X0) X0
               grind)
            | (have r₁ := b4e8762 x
               have r₂ := b4e6963 (σ x) (σ x) x
               grind)
            | exact resolve b4e8762 b4e6963
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6963 b4e8762
          have b4e8820 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e8802 X0
               have i₂ := b4e242 X0
               grind)
            | exact superpose b4e242 b4e8802
            | (have j0 := b4e8802 X0
               grind)
            | exact resolve b4e8802 b4e242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e242 b4e8802
          have b4e338407 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e15 (M.op (σ X0) (σ X0))
               have i₂ := b4e8820 X0
               grind)
            | exact superpose b4e8820 b4e15
            | (have j1 := b4e8820 X0
               grind)
            | exact resolve b4e15 b4e8820
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8820
          have b4e462168 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e6270 (σ X0) (σ X0)
               have i₂ := b4e338407 X0
               grind)
            | exact superpose b4e338407 b4e6270
            | (have j1 := b4e338407 X0
               grind)
            | exact resolve b4e6270 b4e338407
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6270 b4e338407
          have b4e462207 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b4e462168 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e462168
          have b4e467777 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e27
               have i₂ := b4e462207 x
               grind)
            | exact superpose b4e462207 b4e27
            | (have r₁ := b4e27
               have r₂ := b4e462207 x
               grind)
            | exact resolve b4e27 b4e462207
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e462207
          have b4e468021 : False := by grind
          exact b4e468021
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ (M.op y y) := by grind
          have b5e22 : (M.op x y) = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e20
            | exact resolve b5e20 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op (M.op X1 X0) X1) X3
               have i₂ := b5e13 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e31 X0 X1 x X3
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e31
            | exact resolve b5e31 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e50 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e68 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op y y) ∨ y = (k x y) := by
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
          have b5e73 : x = (M.op y y) ∨ y = (k x y) := by grind
          clear b5e68
          have b5e77 : y = (k x y) := by
            first
            | (have r₁ := b5e73
               have r₂ := b5e21
               grind)
            | exact resolve b5e73 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e105 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 (M.op (σ y) (σ y)) x
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
          have b5e106 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
               have r₂ := b5e18 (M.op X1 X1) X1
               grind)
            | (have r₁ := b5e17 X1 X1
               have r₂ := b5e18 (M.op X1 X1) X1
               grind)
            | (have r₁ := b5e17 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | exact resolve b5e17 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e123 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e106 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e106
          have b5e124 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e123 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e123
          have b5e1195 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e105 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e105
          have b5e1196 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1195
               have r₂ := b5e24
               grind)
            | exact resolve b5e1195 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1195
          have b5e1197 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1196
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1196
            | exact resolve b5e1196 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1196
          have b5e1198 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1197
               have i₂ := b5e77
               grind)
            | exact superpose b5e77 b5e1197
            | exact resolve b5e1197 b5e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77 b5e1197
          have b5e1200 : (σ y) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e26
               have i₂ := b5e1198
               grind)
            | exact superpose b5e1198 b5e26
            | exact resolve b5e26 b5e1198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26
          have b5e1205 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e32 (σ x) (σ y) x
               have i₂ := b5e1198
               grind)
            | exact superpose b5e1198 b5e32
            | exact resolve b5e32 b5e1198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1198
          have b5e1410 : ∀ X0 : G, (σ y) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e124 X0 (σ y)
               have i₂ := b5e1205 (σ y)
               grind)
            | exact superpose b5e1205 b5e124
            | (have j0 := b5e124 X0 (σ y)
               grind)
            | exact resolve b5e124 b5e1205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e124
          have b5e1438 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ y) = X0 ∨ (σ y) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e1410 X0
               have i₂ := b5e1205 X0
               grind)
            | exact superpose b5e1205 b5e1410
            | (have j0 := b5e1410 X0
               grind)
            | exact resolve b5e1410 b5e1205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1205 b5e1410
          have b5e1439 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have j0 := b5e1438 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1438
          have b5e2225 : ∀ X0 : G, (σ y) = (σ (k X0 y)) ∨ (σ X0) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 y
               have i₂ := b5e1439 (σ X0)
               grind)
            | exact superpose b5e1439 b5e19
            | (have j1 := b5e1439 (σ (k X0 y))
               grind)
            | exact resolve b5e19 b5e1439
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1439
          have b5e4980 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e2225 (M.op y y)
               have i₂ := b5e50 y
               grind)
            | exact superpose b5e50 b5e2225
            | (have j0 := b5e2225 (M.op y y)
               grind)
            | exact resolve b5e2225 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e2225
          have b5e5006 : (σ y) = (σ (M.op y y)) := by grind
          clear b5e4980
          have b5e5114 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b5e14 (M.op y y)
               have i₂ := b5e5006
               grind)
            | exact superpose b5e5006 b5e14
            | exact resolve b5e14 b5e5006
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5006
          have b5e5150 : y = (M.op y y) := by
            first
            | (have i₁ := b5e5114
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e5114
            | exact resolve b5e5114 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5114
          have b5e5552 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e32 y y x
               have i₂ := b5e5150
               grind)
            | exact superpose b5e5150 b5e32
            | exact resolve b5e32 b5e5150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e5150
          have b5e5805 : y = (M.op x x) := by
            first
            | (have i₁ := b5e22
               have i₂ := b5e5552 x
               grind)
            | exact superpose b5e5552 b5e22
            | exact resolve b5e22 b5e5552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5552
          have b5e5972 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e1200
               have i₂ := b5e5805
               grind)
            | exact superpose b5e5805 b5e1200
            | exact resolve b5e1200 b5e5805
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1200 b5e5805
          have b5e5995 : False := by grind
          exact b5e5995
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op y y) := by grind
        have b6e21 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e28 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X2 (M.op (M.op X1 X0) X1) X3
             have i₂ := b6e12 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e29 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b6e28 X0 X1 x X3
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e28
          | exact resolve b6e28 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e30 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e29 (σ y) (σ y) x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e29
          | exact resolve b6e29 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e38 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        have b6e50 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b6e38
             have i₂ := b6e30 (σ x)
             grind)
          | exact superpose b6e30 b6e38
          | exact resolve b6e38 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30 b6e38
        have b6e54 : (σ x) = (σ (k x y)) := by
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
        have b6e57 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e54
             grind)
          | exact superpose b6e54 b6e13
          | exact resolve b6e13 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e58 : x = (k x y) := by
          first
          | (have i₁ := b6e57
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e57
          | exact resolve b6e57 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e120 : x = (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b6e58
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e58
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e58 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e127 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e120
             have r₂ := b6e20
             grind)
          | exact resolve b6e120 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e120
        have b6e148 : x = (M.op x y) := by
          first
          | (have r₁ := b6e127
             have r₂ := b6e21
             grind)
          | exact resolve b6e127 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e127
        have b6e171 : x ≠ (M.op x x) := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e148
             grind)
          | exact superpose b6e148 b6e21
          | exact resolve b6e21 b6e148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e173 : ∀ X0 : G, x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b6e29 x y x
             have i₂ := b6e148
             grind)
          | exact superpose b6e148 b6e29
          | exact resolve b6e29 b6e148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29 b6e148
        have b6e177 : False := by grind
        exact b6e177
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ (M.op y y) := by grind
          have b7e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e20
            | exact resolve b7e20 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 (τ X0) X1
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e19
            | exact resolve b7e19 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 (M.op (M.op X1 X0) X1) X3
               have i₂ := b7e13 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e31 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b7e30 X0 X1 x X3
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e30
            | exact resolve b7e30 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e60 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b7e80 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e85 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e80
          have b7e89 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e85
               have r₂ := b7e23
               grind)
            | exact resolve b7e85 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e93 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e89
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e89
            | exact resolve b7e89 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e98 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e93
               grind)
            | exact superpose b7e93 b7e14
            | exact resolve b7e14 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e99 : y = (k x y) := by
            first
            | (have i₁ := b7e98
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e98
            | exact resolve b7e98 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98
          have b7e146 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e93
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e93
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e93 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93
          have b7e151 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b7e146
               have r₂ := b7e21
               grind)
            | exact resolve b7e146 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e146
          have b7e172 : (σ (M.op x y)) = (σ y) := by
            first
            | (have r₁ := b7e151
               have r₂ := b7e22
               grind)
            | exact resolve b7e151 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e151
          have b7e195 : y = (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e99
               grind)
            | exact superpose b7e99 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99
          have b7e196 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b7e195
               have r₂ := b7e21
               grind)
            | exact resolve b7e195 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e195
          have b7e198 : y = (M.op x y) := by
            first
            | (have r₁ := b7e196
               have r₂ := b7e22
               grind)
            | exact resolve b7e196 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e196
          have b7e204 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k (τ X0) X1)
               have i₂ := b7e27 X0 X1
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e207 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e31 x y x
               have i₂ := b7e198
               grind)
            | exact superpose b7e198 b7e31
            | exact resolve b7e31 b7e198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e198
          have b7e234 : ∀ X0 : G, (M.op X0 X0) = y ∨ (M.op y y) = X0 ∨ y = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b7e18 X0 y
               have i₂ := b7e207 X0
               grind)
            | exact superpose b7e207 b7e18
            | (have j0 := b7e18 y X0
               grind)
            | exact resolve b7e18 b7e207
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e235 : ∀ X0 : G, (M.op X0 X0) ≠ y ∨ (M.op y y) = X0 ∨ y = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b7e17 X0 y
               have i₂ := b7e207 X0
               grind)
            | exact superpose b7e207 b7e17
            | (have j0 := b7e17 X0 y
               grind)
            | exact resolve b7e17 b7e207
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e238 : ∀ X0 : G, (M.op X0 X0) ≠ y ∨ y = X0 ∨ y = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b7e235 X0
               have i₂ := b7e207 y
               grind)
            | exact superpose b7e207 b7e235
            | (have j0 := b7e235 X0
               grind)
            | (have r₁ := b7e235 y
               have r₂ := b7e207 y
               grind)
            | exact resolve b7e235 b7e207
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e235
          have b7e239 : ∀ X0 : G, y = X0 ∨ (M.op X0 X0) = y ∨ y = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b7e234 X0
               have i₂ := b7e207 y
               grind)
            | exact superpose b7e207 b7e234
            | (have j0 := b7e234 X0
               grind)
            | exact resolve b7e234 b7e207
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e207 b7e234
          have b7e243 : ∀ X0 : G, y = (k X0 y) ∨ y = X0 := by
            intro X0
            first
            | (have j0 := b7e239 X0
               have j1 := b7e238 X0
               grind)
            | (have r₁ := b7e239 (M.op X0 X0)
               have r₂ := b7e238 X0
               grind)
            | (have r₁ := b7e239 X0
               have r₂ := b7e238 X0
               grind)
            | exact resolve b7e239 b7e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e238 b7e239
          have b7e812 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b7e204 (M.op (σ X0) (σ X0)) X0
               have i₂ := b7e60 (σ X0)
               grind)
            | exact superpose b7e60 b7e204
            | exact resolve b7e204 b7e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60 b7e204
          have b7e276081 : y = (τ (M.op (σ y) (σ y))) ∨ y = (τ (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b7e243 (τ (M.op (σ y) (σ y)))
               have i₂ := b7e812 y
               grind)
            | exact superpose b7e812 b7e243
            | (have j0 := b7e243 (τ (M.op (σ y) (σ y)))
               grind)
            | exact resolve b7e243 b7e812
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e243 b7e812
          have b7e276111 : y = (τ (M.op (σ y) (σ y))) := by grind
          clear b7e276081
          have b7e281597 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e15 (M.op (σ y) (σ y))
               have i₂ := b7e276111
               grind)
            | exact superpose b7e276111 b7e15
            | exact resolve b7e15 b7e276111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e276111
          have b7e284915 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e31 (σ y) (σ y) x
               have i₂ := b7e281597
               grind)
            | exact superpose b7e281597 b7e31
            | exact resolve b7e31 b7e281597
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e281597
          have b7e295209 : (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e284915 (σ x)
               grind)
            | exact superpose b7e284915 b7e24
            | exact resolve b7e24 b7e284915
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e284915
          have b7e298722 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b7e26
               have i₂ := b7e295209
               grind)
            | exact superpose b7e295209 b7e26
            | exact resolve b7e26 b7e295209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e295209
          have b7e298797 : False := by grind
          exact b7e298797
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y y) := by grind
          have b8e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e113 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1012 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e113 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113
          have b8e1013 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1012
               have r₂ := b8e24
               grind)
            | exact resolve b8e1012 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1012
          have b8e1014 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1013
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1013
            | exact resolve b8e1013 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1013
          have b8e1016 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1014
               grind)
            | exact superpose b8e1014 b8e20
            | exact resolve b8e20 b8e1014
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1014
          have b8e1059 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e1016
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1016
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1016 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1016
          have b8e1060 : x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e1059
          have b8e1065 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b8e1060
               have r₂ := b8e21
               grind)
            | exact resolve b8e1060 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1060
          have b8e1070 : False := by grind
          exact b8e1070

/-- `Equation3617`: `x ◇ y = z ◇ ((z ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_pxx_pxy_Equation3617 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3617 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3617.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op x y) := by grind
      have b0e18 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e19 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e16
        | exact resolve b0e16 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e20 : (σ y) ≠ (σ y) := by
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
      have b0e21 : False := by grind
      exact b0e21
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X2 X0) X1)) := by
        intro X0 X1 X2
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e17 : y = (M.op x y) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
      have b1e21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e15
        | exact resolve b1e15 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e22 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b1e10 y X0 x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X2 (M.op (M.op X0 X1) X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 (M.op (M.op X2 X0) X1) X3 X2
           have i₂ := b1e10 X0 X1 X2
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op X3 X2) X0) X1)) = (M.op X3 (M.op X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X2 (M.op (M.op (M.op X3 X2) X0) X1) X3
           have i₂ := b1e10 X0 X1 (M.op X3 X2)
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e25 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e22 (M.op (M.op y X0) X1)
           have i₂ := b1e10 X0 X1 y
           grind)
        | exact superpose b1e10 b1e22
        | exact resolve b1e22 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e27 : y ≠ y ∨ (k x y) = (M.op x x) := by
        first
        | (have i₁ := b1e13 x y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e13
        | (have j0 := b1e13 x y
           grind)
        | (have r₁ := b1e13 x y
           have r₂ := b1e17
           grind)
        | exact resolve b1e13 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e31 : (k x y) = (M.op x x) := by grind
      clear b1e27
      have b1e34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b1e41 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 X1 x
           have i₂ := b1e25 (M.op x X0) X1
           grind)
        | exact superpose b1e25 b1e10
        | exact resolve b1e10 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e42 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op x x) = (k x (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 x (M.op X0 X1)
           have i₂ := b1e25 X0 X1
           grind)
        | exact superpose b1e25 b1e13
        | (have j0 := b1e13 x (M.op X0 X1)
           grind)
        | (have r₁ := b1e13 x (M.op X0 X1)
           have r₂ := b1e25 X0 X1
           grind)
        | exact resolve b1e13 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e44 : ∀ X0 X1 : G, (M.op x x) = (k x (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have j0 := b1e42 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e42
      have b1e49 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k (τ X0) X1)
           have i₂ := b1e20 X0 X1
           grind)
        | exact superpose b1e20 b1e11
        | exact resolve b1e11 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20
      have b1e59 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k X0 (τ X1))
           have i₂ := b1e21 X1 X0
           grind)
        | exact superpose b1e21 b1e11
        | exact resolve b1e11 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21
      have b1e81 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X4) = (M.op (M.op X0 X1) (M.op (M.op X2 X3) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e23 X2 X3 (M.op X0 X1) X4
           have i₂ := b1e23 X1 X2 X0 X3
           grind)
        | exact superpose b1e23 b1e23
        | exact resolve b1e23 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e84 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X2) X3))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X2 X3 (M.op X0 X1)
           have i₂ := b1e23 X1 X2 X0 X3
           grind)
        | exact superpose b1e23 b1e10
        | exact resolve b1e10 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e119 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X3)) = (M.op X1 (M.op X0 (M.op (M.op X1 X2) X3))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e24 X2 X3 X1 X0
           have i₂ := b1e23 X1 X2 X0 X3
           grind)
        | exact superpose b1e23 b1e24
        | exact resolve b1e24 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e121 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X4 (M.op X5 (M.op (M.op (M.op X0 (M.op (M.op X4 X3) X5)) X1) X2))) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b1e24 X5 (M.op (M.op (M.op X0 (M.op (M.op X4 X3) X5)) X1) X2) X3 X4
           have i₂ := b1e24 X1 X2 (M.op (M.op X4 X3) X5) X0
           grind)
        | exact superpose b1e24 b1e24
        | exact resolve b1e24 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e129 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X3) X1) X2) X4) = (M.op X3 (M.op (M.op X0 (M.op X1 X2)) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e10 (M.op (M.op (M.op X0 X3) X1) X2) X4 X3
           have i₂ := b1e24 X1 X2 X3 X0
           grind)
        | exact superpose b1e24 b1e10
        | exact resolve b1e10 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e130 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 X2)) X5) = (M.op X3 (M.op (M.op X4 (M.op (M.op (M.op X0 (M.op X3 X4)) X1) X2)) X5)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b1e23 X4 (M.op (M.op (M.op X0 (M.op X3 X4)) X1) X2) X3 X5
           have i₂ := b1e24 X1 X2 (M.op X3 X4) X0
           grind)
        | exact superpose b1e24 b1e23
        | exact resolve b1e23 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e131 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op (M.op X0 (M.op X4 X3)) X1) X2)) = (M.op X4 (M.op X0 (M.op X1 X2))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e10 X3 (M.op (M.op (M.op X0 (M.op X4 X3)) X1) X2) X4
           have i₂ := b1e24 X1 X2 (M.op X4 X3) X0
           grind)
        | exact superpose b1e24 b1e10
        | exact resolve b1e10 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e142 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op X0 (M.op (M.op (M.op X4 X3) X1) X2))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e131 X0 X1 X2 X3 X4
           have i₂ := b1e23 (M.op X4 X3) X1 X0 X2
           grind)
        | exact superpose b1e23 b1e131
        | exact resolve b1e131 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e131
      have b1e143 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 X2)) X5) = (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X3 X4))) (M.op (M.op X1 X2) X5))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b1e130 X0 X1 X2 X3 X4 X5
           have i₂ := b1e81 X4 (M.op X0 (M.op X3 X4)) X1 X2 X5
           grind)
        | exact superpose b1e81 b1e130
        | exact resolve b1e130 b1e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e81 b1e130
      have b1e144 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 (M.op X1 X2)) X4)) = (M.op (M.op X0 X3) (M.op (M.op X1 X2) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e129 X0 X1 X2 X3 X4
           have i₂ := b1e23 X1 X2 (M.op X0 X3) X4
           grind)
        | exact superpose b1e23 b1e129
        | exact resolve b1e129 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e129
      have b1e150 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X4 (M.op X5 (M.op X0 (M.op (M.op (M.op (M.op X4 X3) X5) X1) X2)))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b1e121 X0 X1 X2 X3 X4 X5
           have i₂ := b1e23 (M.op (M.op X4 X3) X5) X1 X0 X2
           grind)
        | exact superpose b1e23 b1e121
        | exact resolve b1e121 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e121
      have b1e165 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op X0 (M.op X4 (M.op (M.op X3 X1) X2)))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e142 X0 X1 X2 X3 X4
           have i₂ := b1e23 X3 X1 X4 X2
           grind)
        | exact superpose b1e23 b1e142
        | exact resolve b1e142 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e142
      have b1e170 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X4 (M.op X5 (M.op X0 (M.op (M.op X4 X3) (M.op (M.op X5 X1) X2))))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b1e150 X0 X1 X2 X3 X4 X5
           have i₂ := b1e23 X5 X1 (M.op X4 X3) X2
           grind)
        | exact superpose b1e23 b1e150
        | exact resolve b1e150 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e150
      have b1e179 : ∀ X0 X1 X2 X3 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X0 (M.op X5 (M.op X3 (M.op (M.op X5 X1) X2)))) := by
        intro X0 X1 X2 X3 X5
        first
        | (have i₁ := b1e170 X0 X1 X2 X3 x X5
           have i₂ := b1e165 X5 X3 (M.op (M.op X5 X1) X2) x X0
           grind)
        | exact superpose b1e165 b1e170
        | exact resolve b1e170 b1e165
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e165 b1e170
      have b1e181 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X0 (M.op X3 (M.op X1 X2))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e179 X0 X1 X2 X3 x
           have i₂ := b1e119 X3 x X1 X2
           grind)
        | exact superpose b1e119 b1e179
        | exact resolve b1e179 b1e119
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e179
      have b1e183 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e49 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e49
        | exact resolve b1e49 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e49
      have b1e202 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op x (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e25 (σ X0) (σ X1)
           have i₂ := b1e34 X0 X1
           grind)
        | exact superpose b1e34 b1e25
        | (have j1 := b1e34 X0 X1
           grind)
        | exact resolve b1e25 b1e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25
      have b1e203 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 (σ X0) (σ X1)
           have i₂ := b1e34 X0 X1
           grind)
        | exact superpose b1e34 b1e13
        | (have j0 := b1e13 (σ X0) (σ X1)
           have j1 := b1e34 X0 X1
           grind)
        | (have r₁ := b1e13 (σ X0) (σ X1)
           have r₂ := b1e34 X0 X1
           grind)
        | exact resolve b1e13 b1e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e204 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ X0) (M.op (σ (k X0 X1)) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (σ X1) X2 (σ X0)
           have i₂ := b1e34 X0 X1
           grind)
        | exact superpose b1e34 b1e10
        | (have j1 := b1e34 X0 X1
           grind)
        | exact resolve b1e10 b1e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e205 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b1e34 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e206 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e203 X0 X1
           have j1 := b1e13 (σ X0) (σ X1)
           grind)
        | (have r₁ := b1e203 X0 X1
           have r₂ := b1e13 (σ X0) (σ X1)
           grind)
        | exact resolve b1e203 b1e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e203
      have b1e209 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e206 X0 X1
           have i₂ := b1e15 X0 X1
           grind)
        | exact superpose b1e15 b1e206
        | (have j0 := b1e206 X0 X1
           grind)
        | exact resolve b1e206 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e206
      have b1e214 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e59 X0 X1
           have i₂ := b1e14 (σ X0) X1
           grind)
        | exact superpose b1e14 b1e59
        | (have j1 := b1e14 (σ X0) X1
           grind)
        | exact resolve b1e59 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e388 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e84 X2 X2 X0 X1
           have i₂ := b1e10 X0 X1 X2
           grind)
        | exact superpose b1e10 b1e84
        | exact resolve b1e84 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e389 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X0 X3)) (M.op X0 (M.op X1 X2))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e84 X3 (M.op X0 X3) X1 X2
           have i₂ := b1e24 X1 X2 X3 X0
           grind)
        | exact superpose b1e24 b1e84
        | exact resolve b1e84 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e24
      have b1e390 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op (M.op (M.op (M.op X4 X2) X3) X4) (M.op X0 X1)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e84 (M.op (M.op X4 X2) X3) X4 X2 (M.op (M.op X3 X0) X1)
           have i₂ := b1e84 (M.op X4 X2) X3 X0 X1
           grind)
        | exact superpose b1e84 b1e84
        | exact resolve b1e84 b1e84
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e425 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op (M.op X4 X2) (M.op (M.op X3 X4) (M.op X0 X1))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e390 X0 X1 X2 X3 X4
           have i₂ := b1e23 X3 X4 (M.op X4 X2) (M.op X0 X1)
           grind)
        | exact superpose b1e23 b1e390
        | exact resolve b1e390 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e390
      have b1e426 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op (M.op X3 (M.op X0 X3)) (M.op X1 X2))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e389 X0 X1 X2 X3
           have i₂ := b1e181 X0 X1 X2 (M.op X3 (M.op X0 X3))
           grind)
        | (have i₁ := b1e389 X0 X1 X2 X3
           have i₂ := b1e181 (M.op X3 (M.op X0 X3)) X1 X2 X0
           grind)
        | exact superpose b1e181 b1e389
        | exact resolve b1e389 b1e181
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e389
      have b1e456 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X2 (M.op (M.op X4 (M.op X3 X4)) (M.op X0 X1))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e425 X0 X1 X2 X3 X4
           have i₂ := b1e144 X4 X3 X4 X2 (M.op X0 X1)
           grind)
        | (have i₁ := b1e425 X0 X1 X2 X0 (M.op X1 X2)
           have i₂ := b1e144 X0 X1 X2 (M.op (M.op X1 X2) X2) (M.op X0 X1)
           grind)
        | exact superpose b1e144 b1e425
        | exact resolve b1e425 b1e144
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e425
      have b1e534 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op (M.op X0 X1) (M.op X2 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X1 (M.op (M.op X0 X2) X3) X0
           have i₂ := b1e119 (M.op X0 X1) X0 X2 X3
           grind)
        | exact superpose b1e119 b1e10
        | exact resolve b1e10 b1e119
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e666 : ∀ X0 : G, y = (M.op (M.op X0 X0) y) := by
        intro X0
        first
        | (have i₁ := b1e388 x y x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e388
        | exact resolve b1e388 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e757 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X1 (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e181 X0 x y x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e181
        | exact resolve b1e181 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e971 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op X1 (M.op X0 X1)) y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e23 X1 (M.op X0 X1) X0 y
           have i₂ := b1e666 (M.op X0 X1)
           grind)
        | exact superpose b1e666 b1e23
        | exact resolve b1e23 b1e666
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e666
      have b1e1005 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e205 (τ X0) (τ X1)
           have i₂ := b1e183 X1 X0
           grind)
        | exact superpose b1e183 b1e205
        | (have j0 := b1e205 (τ X0) (τ X1)
           grind)
        | exact resolve b1e205 b1e183
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1010 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op x x)) ∨ (σ (M.op X0 X1)) = (M.op (σ x) (σ (M.op X0 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e205 x (M.op X0 X1)
           have i₂ := b1e44 X0 X1
           grind)
        | exact superpose b1e44 b1e205
        | (have j0 := b1e205 x (M.op X0 X1)
           grind)
        | exact resolve b1e205 b1e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1016 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e1005 X0 X1
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e1005
        | (have j0 := b1e1005 X0 X1
           grind)
        | exact resolve b1e1005 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1005
      have b1e1018 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e1016 X0 X1
           have i₂ := b1e12 X1
           grind)
        | exact superpose b1e12 b1e1016
        | (have j0 := b1e1016 X0 X1
           grind)
        | exact resolve b1e1016 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1016
      have b1e1019 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e1018 X0 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e1018
        | (have j0 := b1e1018 X0 X1
           grind)
        | exact resolve b1e1018 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1018
      have b1e1020 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e1019 X0 X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e1019
        | (have j0 := b1e1019 X0 X1
           grind)
        | exact resolve b1e1019 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1019
      have b1e1192 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
        intro X0 X1
        first
        | (have i₁ := b1e209 x (M.op X0 X1)
           have i₂ := b1e44 X0 X1
           grind)
        | exact superpose b1e44 b1e209
        | exact resolve b1e209 b1e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e44 b1e209
      have b1e1775 : ∀ X0 X1 : G, (M.op X0 y) ≠ (M.op X0 (M.op X1 y)) ∨ (M.op X1 X1) = (k X1 (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 X1 (M.op X0 y)
           have i₂ := b1e757 X1 X0
           grind)
        | (have i₁ := b1e13 X1 (M.op X0 y)
           have i₂ := b1e757 X0 X1
           grind)
        | exact superpose b1e757 b1e13
        | (have j0 := b1e13 X1 (M.op X0 y)
           grind)
        | exact resolve b1e13 b1e757
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e757
      have b1e4094 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op (σ (M.op x x)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e204 x y X0
           have i₂ := b1e31
           grind)
        | exact superpose b1e31 b1e204
        | (have j0 := b1e204 x y x
           grind)
        | exact resolve b1e204 b1e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e204
      have b1e4155 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op (σ (M.op x x)) X0)) := by
        intro X0
        first
        | (have j0 := b1e4094 X0
           grind)
        | (have r₁ := b1e4094 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e4094 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4094
      have b1e4297 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op x X0)) X1) = (M.op X3 (M.op (M.op X4 (M.op X2 (M.op X3 X4))) (M.op X0 X1))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e143 X2 x X0 X3 X4 X1
           have i₂ := b1e41 X0 X1
           grind)
        | exact superpose b1e41 b1e143
        | exact resolve b1e143 b1e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e41
      have b1e4302 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 (M.op X3 X3)) (M.op X0 X1)) = (M.op X4 (M.op (M.op X5 (M.op X2 (M.op X4 X5))) (M.op X0 X1))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b1e143 X2 X3 X3 X4 X5 (M.op X0 X1)
           have i₂ := b1e388 X0 X1 X3
           grind)
        | exact superpose b1e388 b1e143
        | exact resolve b1e143 b1e388
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e143 b1e388
      have b1e4492 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 (M.op X3 X3)) (M.op X0 X1)) = (M.op X4 (M.op (M.op X2 (M.op X4 X5)) (M.op (M.op X5 X0) X1))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b1e4302 X0 X1 X2 X3 X4 X5
           have i₂ := b1e534 X5 (M.op X2 (M.op X4 X5)) X0 X1
           grind)
        | exact superpose b1e534 b1e4302
        | exact resolve b1e4302 b1e534
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4302
      have b1e4497 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op x X0)) X1) = (M.op X3 (M.op (M.op X2 (M.op X3 X4)) (M.op (M.op X4 X0) X1))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e4297 X0 X1 X2 X3 X4
           have i₂ := b1e534 X4 (M.op X2 (M.op X3 X4)) X0 X1
           grind)
        | exact superpose b1e534 b1e4297
        | exact resolve b1e4297 b1e534
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4297
      have b1e4645 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 (M.op X3 X3)) (M.op X0 X1)) = (M.op X4 (M.op (M.op X4 X5) (M.op (M.op X2 (M.op X5 X0)) X1))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b1e4492 X0 X1 X2 X3 X4 X5
           have i₂ := b1e144 X2 X5 X0 (M.op X4 X5) X1
           grind)
        | (have i₁ := b1e4492 (M.op X1 X2) X4 X2 X3 X4 X0
           have i₂ := b1e144 X0 X1 X2 (M.op X2 (M.op X4 X0)) X4
           grind)
        | exact superpose b1e144 b1e4492
        | exact resolve b1e4492 b1e144
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4492
      have b1e4650 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op x X0)) X1) = (M.op X3 (M.op (M.op X3 X4) (M.op (M.op X2 (M.op X4 X0)) X1))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e4497 X0 X1 X2 X3 X4
           have i₂ := b1e144 X2 X4 X0 (M.op X3 X4) X1
           grind)
        | (have i₁ := b1e4497 (M.op X1 X2) X4 X2 X3 X0
           have i₂ := b1e144 X0 X1 X2 (M.op X2 (M.op X3 X0)) X4
           grind)
        | exact superpose b1e144 b1e4497
        | exact resolve b1e4497 b1e144
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4497
      have b1e4787 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 (M.op X3 X3)) (M.op X0 X1)) = (M.op X5 (M.op (M.op X2 (M.op X5 X0)) X1)) := by
        intro X0 X1 X2 X3 X5
        first
        | (have i₁ := b1e4645 X0 X1 X2 X3 x X5
           have i₂ := b1e10 X5 (M.op (M.op X2 (M.op X5 X0)) X1) x
           grind)
        | exact superpose b1e10 b1e4645
        | exact resolve b1e4645 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4645
      have b1e4792 : ∀ X0 X1 X2 X4 : G, (M.op X4 (M.op (M.op X2 (M.op X4 X0)) X1)) = (M.op (M.op X2 (M.op x X0)) X1) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b1e4650 X0 X1 X2 x X4
           have i₂ := b1e10 X4 (M.op (M.op X2 (M.op X4 X0)) X1) x
           grind)
        | exact superpose b1e10 b1e4650
        | exact resolve b1e4650 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4650
      have b1e4897 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 X3) (M.op (M.op X2 X0) X1)) = (M.op X5 (M.op (M.op X2 (M.op X5 X0)) X1)) := by
        intro X0 X1 X2 X3 X5
        first
        | (have i₁ := b1e4787 X0 X1 X2 X3 X5
           have i₂ := b1e534 X2 (M.op X3 X3) X0 X1
           grind)
        | exact superpose b1e534 b1e4787
        | exact resolve b1e4787 b1e534
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4787
      have b1e4989 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op X2 X0) X1)) = (M.op (M.op X2 (M.op x X0)) X1) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e4897 X0 X1 X2 X3 x
           have i₂ := b1e4792 X0 X1 X2 x
           grind)
        | exact superpose b1e4792 b1e4897
        | exact resolve b1e4897 b1e4792
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4897
      have b1e5061 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op x X0)) X1) = (M.op X3 (M.op (M.op X3 (M.op X2 X0)) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e4989 X0 X1 X2 X3
           have i₂ := b1e144 X3 X2 X0 X3 X1
           grind)
        | (have i₁ := b1e4989 (M.op X1 X2) x X0 X3
           have i₂ := b1e144 X0 X1 X2 (M.op X3 X3) x
           grind)
        | exact superpose b1e144 b1e4989
        | exact resolve b1e4989 b1e144
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4989
      have b1e5124 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op (M.op X2 (M.op x X0)) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e5061 X0 X1 X2 x
           have i₂ := b1e10 (M.op X2 X0) X1 x
           grind)
        | exact superpose b1e10 b1e5061
        | exact resolve b1e5061 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5061
      have b1e9047 : ∀ X0 X1 : G, (M.op (σ x) (M.op X1 (M.op (σ (M.op x x)) X0))) = (M.op X1 (M.op (σ y) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e181 (σ x) (σ (M.op x x)) X0 X1
           have i₂ := b1e4155 X0
           grind)
        | exact superpose b1e4155 b1e181
        | exact resolve b1e181 b1e4155
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e181
      have b1e14415 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e214 (τ X0) X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e214
        | exact resolve b1e214 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e14464 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e14415 X0 X1
           have i₂ := b1e183 X1 X0
           grind)
        | exact superpose b1e183 b1e14415
        | (have j0 := b1e14415 X0 X1
           grind)
        | exact resolve b1e14415 b1e183
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e183 b1e14415
      have b1e15108 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e14464 (σ X0) (σ X1)
           have i₂ := b1e15 X0 X1
           grind)
        | exact superpose b1e15 b1e14464
        | (have j0 := b1e14464 (σ X0) (σ X1)
           grind)
        | exact resolve b1e14464 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e14464
      have b1e15149 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15108 X0 X1
           have i₂ := b1e11 (k X0 X1)
           grind)
        | exact superpose b1e11 b1e15108
        | (have j0 := b1e15108 X0 X1
           grind)
        | exact resolve b1e15108 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e15108
      have b1e169170 : (M.op x y) ≠ (M.op y y) ∨ (M.op y y) = (k y (M.op x y)) := by
        first
        | (have i₁ := b1e1775 x y
           have i₂ := b1e22 y
           grind)
        | exact superpose b1e22 b1e1775
        | (have j0 := b1e1775 x y
           grind)
        | exact resolve b1e1775 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22 b1e1775
      have b1e169177 : y ≠ (M.op y y) ∨ (M.op y y) = (k y (M.op x y)) := by
        first
        | (have i₁ := b1e169170
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e169170
        | exact resolve b1e169170 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e169170
      have b1e169187 : (M.op y y) = (k y y) ∨ y ≠ (M.op y y) := by
        first
        | (have i₁ := b1e169177
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e169177
        | exact resolve b1e169177 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e169177
      have b1e169192 : (M.op y y) = (k y y) := by
        first
        | (have j1 := b1e14 y y
           grind)
        | (have r₁ := b1e169187
           have r₂ := b1e14 y y
           grind)
        | exact resolve b1e169187 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e169187
      have b1e186287 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op X1 (σ (M.op x x))) X2)) = (M.op (M.op X0 (M.op X1 X0)) (M.op (σ y) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e456 (σ (M.op x x)) X2 (σ x) X1 X0
           have i₂ := b1e9047 X2 (M.op X0 (M.op X1 X0))
           grind)
        | exact superpose b1e9047 b1e456
        | exact resolve b1e456 b1e9047
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e456
      have b1e186288 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) X1) = (M.op (M.op X0 (M.op (σ x) X0)) (M.op (σ y) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e426 (σ x) (σ (M.op x x)) X1 X0
           have i₂ := b1e9047 X1 (M.op X0 (M.op (σ x) X0))
           grind)
        | exact superpose b1e9047 b1e426
        | exact resolve b1e426 b1e9047
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e426 b1e9047
      have b1e186332 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) X1) = (M.op (M.op (σ x) X0) (M.op (M.op X0 (σ y)) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e186288 X0 X1
           have i₂ := b1e534 X0 (M.op (σ x) X0) (σ y) X1
           grind)
        | exact superpose b1e534 b1e186288
        | exact resolve b1e186288 b1e534
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e186288
      have b1e186333 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op X1 (σ (M.op x x))) X2)) = (M.op (M.op X1 X0) (M.op (M.op X0 (σ y)) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e186287 X0 X1 X2
           have i₂ := b1e534 X0 (M.op X1 X0) (σ y) X2
           grind)
        | exact superpose b1e534 b1e186287
        | exact resolve b1e186287 b1e534
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e534 b1e186287
      have b1e186410 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) X1) = (M.op X0 (M.op (M.op (σ x) (M.op X0 (σ y))) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e186332 X0 X1
           have i₂ := b1e144 (σ x) X0 (σ y) X0 X1
           grind)
        | exact superpose b1e144 b1e186332
        | exact resolve b1e186332 b1e144
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e186332
      have b1e186411 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op X1 (σ (M.op x x))) X2)) = (M.op X0 (M.op (M.op X1 (M.op X0 (σ y))) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e186333 X0 X1 X2
           have i₂ := b1e144 X1 X0 (σ y) X0 X2
           grind)
        | exact superpose b1e144 b1e186333
        | exact resolve b1e186333 b1e144
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e144 b1e186333
      have b1e186442 : ∀ X1 : G, (M.op (σ (M.op x x)) X1) = (M.op (M.op (σ x) (M.op x (σ y))) X1) := by
        intro X1
        first
        | (have i₁ := b1e186410 x X1
           have i₂ := b1e4792 (σ y) X1 (σ x) x
           grind)
        | exact superpose b1e4792 b1e186410
        | exact resolve b1e186410 b1e4792
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e186410
      have b1e186443 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op X1 (σ (M.op x x))) X2)) = (M.op (M.op X1 (M.op x (σ y))) X2) := by
        intro X1 X2
        first
        | (have i₁ := b1e186411 x X1 X2
           have i₂ := b1e4792 (σ y) X2 X1 x
           grind)
        | exact superpose b1e4792 b1e186411
        | exact resolve b1e186411 b1e4792
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4792 b1e186411
      have b1e186458 : ∀ X1 : G, (M.op (σ (M.op x x)) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
        intro X1
        first
        | (have i₁ := b1e186442 X1
           have i₂ := b1e5124 (σ y) X1 (σ x)
           grind)
        | exact superpose b1e5124 b1e186442
        | exact resolve b1e186442 b1e5124
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e186442
      have b1e186459 : ∀ X1 X2 : G, (M.op (M.op X1 (σ y)) X2) = (M.op (σ x) (M.op (M.op X1 (σ (M.op x x))) X2)) := by
        intro X1 X2
        first
        | (have i₁ := b1e186443 X1 X2
           have i₂ := b1e5124 (σ y) X2 X1
           grind)
        | exact superpose b1e5124 b1e186443
        | exact resolve b1e186443 b1e5124
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5124 b1e186443
      have b1e303563 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by grind
      clear b1e1192
      have b1e303941 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x x)) X0)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b1e10 (σ x) X0 (σ x)
           have i₂ := b1e303563
           grind)
        | exact superpose b1e303563 b1e10
        | exact resolve b1e10 b1e303563
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e303943 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x x)) X0) X1) = (M.op (σ x) (M.op (M.op (σ x) X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e23 (σ x) X0 (σ x) X1
           have i₂ := b1e303563
           grind)
        | exact superpose b1e303563 b1e23
        | exact resolve b1e23 b1e303563
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23 b1e303563
      have b1e304035 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (σ (M.op x x)) X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e303943 X0 X1
           have i₂ := b1e10 X0 X1 (σ x)
           grind)
        | exact superpose b1e10 b1e303943
        | exact resolve b1e303943 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e303943
      have b1e304037 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b1e303941 X0
           have i₂ := b1e4155 X0
           grind)
        | exact superpose b1e4155 b1e303941
        | exact resolve b1e303941 b1e4155
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4155 b1e303941
      have b1e304982 : ∀ X0 : G, (τ (M.op (σ y) X0)) = (k x (τ X0)) ∨ (M.op (σ y) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b1e214 x X0
           have i₂ := b1e304037 X0
           grind)
        | exact superpose b1e304037 b1e214
        | (have j0 := b1e214 y X0
           grind)
        | exact resolve b1e214 b1e304037
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e304998 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (M.op (σ y) (σ y)) X0) := by
        intro X0
        first
        | (have i₁ := b1e186458 X0
           have i₂ := b1e304037 (σ y)
           grind)
        | exact superpose b1e304037 b1e186458
        | exact resolve b1e186458 b1e304037
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e186458
      have b1e305000 : (σ y) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e304037 (σ y)
           grind)
        | exact superpose b1e304037 b1e18
        | exact resolve b1e18 b1e304037
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e336049 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (σ (k y y)) X0) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e304998 X0
           have i₂ := b1e34 y y
           grind)
        | exact superpose b1e34 b1e304998
        | (have j1 := b1e34 y y
           grind)
        | exact resolve b1e304998 b1e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34 b1e304998
      have b1e336355 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (σ (k y y)) X0) := by
        intro X0
        first
        | (have j0 := b1e336049 X0
           grind)
        | (have r₁ := b1e336049 X0
           have r₂ := b1e305000
           grind)
        | exact resolve b1e336049 b1e305000
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e336049
      have b1e336461 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (σ (M.op y y)) X0) := by
        intro X0
        first
        | (have i₁ := b1e336355 X0
           have i₂ := b1e169192
           grind)
        | exact superpose b1e169192 b1e336355
        | exact resolve b1e336355 b1e169192
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e336355
      have b1e337546 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (σ (M.op y y)) X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e304035 X0 X1
           have i₂ := b1e336461 X0
           grind)
        | exact superpose b1e336461 b1e304035
        | exact resolve b1e304035 b1e336461
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e304035 b1e336461
      have b1e373987 : ∀ X0 : G, (k y (τ X0)) = (k x (τ X0)) ∨ (M.op (σ y) X0) = X0 ∨ (M.op (σ y) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b1e214 y X0
           have i₂ := b1e304982 X0
           grind)
        | exact superpose b1e304982 b1e214
        | (have j0 := b1e214 y X0
           have j1 := b1e304982 X0
           grind)
        | exact resolve b1e214 b1e304982
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e214 b1e304982
      have b1e373994 : ∀ X0 : G, (k y (τ X0)) = (k x (τ X0)) ∨ (M.op (σ y) X0) = X0 := by
        intro X0
        first
        | (have j0 := b1e373987 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e373987
      have b1e374520 : ∀ X0 : G, (σ X0) = (M.op (σ y) (σ X0)) ∨ (k y X0) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e373994 (σ X0)
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e373994
        | (have j0 := b1e373994 (σ X0)
           grind)
        | exact resolve b1e373994 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e373994
      have b1e377106 : (σ y) ≠ (σ y) ∨ (k x y) = (k y y) := by
        first
        | (have i₁ := b1e305000
           have i₂ := b1e374520 y
           grind)
        | exact superpose b1e374520 b1e305000
        | (have j1 := b1e374520 y
           grind)
        | (have r₁ := b1e305000
           have r₂ := b1e374520 y
           grind)
        | exact resolve b1e305000 b1e374520
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e374520
      have b1e377152 : (k x y) = (k y y) := by grind
      clear b1e377106
      have b1e377184 : (k x y) = (M.op y y) := by
        first
        | (have i₁ := b1e377152
           have i₂ := b1e169192
           grind)
        | exact superpose b1e169192 b1e377152
        | exact resolve b1e377152 b1e169192
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e377152
      have b1e378221 : (M.op x x) = (M.op y y) := by
        first
        | (have i₁ := b1e31
           have i₂ := b1e377184
           grind)
        | exact superpose b1e377184 b1e31
        | exact resolve b1e31 b1e377184
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e31
      have b1e378240 : (σ (M.op y y)) = (M.op x (σ (M.op y y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e202 x y
           have i₂ := b1e377184
           grind)
        | exact superpose b1e377184 b1e202
        | (have j0 := b1e202 x y
           grind)
        | exact resolve b1e202 b1e377184
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e202
      have b1e378242 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e205 x y
           have i₂ := b1e377184
           grind)
        | exact superpose b1e377184 b1e205
        | (have j0 := b1e205 x y
           grind)
        | exact resolve b1e205 b1e377184
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e205 b1e377184
      have b1e378280 : (σ y) ≠ (σ (M.op y y)) := by
        first
        | (have r₁ := b1e378242
           have r₂ := b1e18
           grind)
        | exact resolve b1e378242 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e378242
      have b1e378282 : (σ (M.op y y)) = (M.op x (σ (M.op y y))) := by
        first
        | (have r₁ := b1e378240
           have r₂ := b1e18
           grind)
        | exact resolve b1e378240 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e378240
      have b1e379322 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (σ x) (M.op (M.op X0 (σ (M.op y y))) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e186459 X0 X1
           have i₂ := b1e378221
           grind)
        | exact superpose b1e378221 b1e186459
        | exact resolve b1e186459 b1e378221
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e186459
      have b1e379576 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (σ y) (M.op (M.op X0 (σ (M.op y y))) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e379322 X0 X1
           have i₂ := b1e304037 (M.op (M.op X0 (σ (M.op y y))) X1)
           grind)
        | exact superpose b1e304037 b1e379322
        | exact resolve b1e379322 b1e304037
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e379322
      have b1e459079 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ x) (σ (M.op y y))) := by
        first
        | (have i₁ := b1e1010 x x
           have i₂ := b1e378221
           grind)
        | exact superpose b1e378221 b1e1010
        | (have j0 := b1e1010 y y
           grind)
        | exact resolve b1e1010 b1e378221
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1010 b1e378221
      have b1e459084 : (σ (M.op y y)) = (M.op (σ x) (σ (M.op y y))) := by grind
      clear b1e459079
      have b1e459087 : (σ (M.op y y)) = (M.op (σ y) (σ (M.op y y))) := by
        first
        | (have i₁ := b1e459084
           have i₂ := b1e304037 (σ (M.op y y))
           grind)
        | exact superpose b1e304037 b1e459084
        | exact resolve b1e459084 b1e304037
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e304037 b1e459084
      have b1e459101 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ (M.op y y)) (M.op (σ y) (M.op (M.op (σ (M.op y y)) X0) X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e84 (σ y) (σ (M.op y y)) X0 X1
           have i₂ := b1e459087
           grind)
        | exact superpose b1e459087 b1e84
        | exact resolve b1e84 b1e459087
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e84
      have b1e459118 : y = (M.op (σ y) (M.op (M.op (σ (M.op y y)) (σ (M.op y y))) y)) := by
        first
        | (have i₁ := b1e971 (σ y) (σ (M.op y y))
           have i₂ := b1e459087
           grind)
        | exact superpose b1e459087 b1e971
        | exact resolve b1e971 b1e459087
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e459087
      have b1e459164 : y = (M.op (M.op (σ (M.op y y)) (σ y)) y) := by
        first
        | (have i₁ := b1e459118
           have i₂ := b1e379576 (σ (M.op y y)) y
           grind)
        | exact superpose b1e379576 b1e459118
        | exact resolve b1e459118 b1e379576
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e379576 b1e459118
      have b1e459172 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ y) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e459101 X0 X1
           have i₂ := b1e119 (σ y) (σ (M.op y y)) X0 X1
           grind)
        | exact superpose b1e119 b1e459101
        | exact resolve b1e459101 b1e119
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e119 b1e459101
      have b1e459189 : y = (M.op (σ y) y) := by
        first
        | (have i₁ := b1e459164
           have i₂ := b1e337546 (σ y) y
           grind)
        | exact superpose b1e337546 b1e459164
        | exact resolve b1e459164 b1e337546
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e337546 b1e459164
      have b1e459252 : y ≠ y ∨ (M.op (σ y) (σ y)) = (k (σ y) y) := by
        first
        | (have i₁ := b1e13 (σ y) y
           have i₂ := b1e459189
           grind)
        | exact superpose b1e459189 b1e13
        | (have j0 := b1e13 (σ y) y
           grind)
        | (have r₁ := b1e13 (σ y) y
           have r₂ := b1e459189
           grind)
        | exact resolve b1e13 b1e459189
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e459189
      have b1e459356 : (M.op (σ y) (σ y)) = (k (σ y) y) := by grind
      clear b1e459252
      have b1e461527 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 (σ y) (M.op X0 X1)
           have i₂ := b1e459172 X0 X1
           grind)
        | exact superpose b1e459172 b1e13
        | (have j0 := b1e13 (σ y) (M.op X0 X1)
           grind)
        | (have r₁ := b1e13 (σ y) (M.op X0 X1)
           have r₂ := b1e459172 X0 X1
           grind)
        | exact resolve b1e13 b1e459172
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e459172
      have b1e461589 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have j0 := b1e461527 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e461527
      have b1e461608 : ∀ X0 X1 : G, (k (σ y) y) = (k (σ y) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e461589 X0 X1
           have i₂ := b1e459356
           grind)
        | exact superpose b1e459356 b1e461589
        | exact resolve b1e461589 b1e459356
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e461589
      have b1e463288 : (σ y) ≠ (k (σ y) y) := by
        first
        | (have i₁ := b1e305000
           have i₂ := b1e459356
           grind)
        | exact superpose b1e459356 b1e305000
        | exact resolve b1e305000 b1e459356
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e305000
      have b1e463291 : (k y y) = (τ (k (σ y) y)) ∨ (σ y) = (k (σ y) y) := by
        first
        | (have i₁ := b1e15149 y y
           have i₂ := b1e459356
           grind)
        | exact superpose b1e459356 b1e15149
        | exact resolve b1e15149 b1e459356
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e15149 b1e459356
      have b1e463459 : (k y y) = (k y (τ y)) ∨ (σ y) = (k (σ y) y) := by
        first
        | (have i₁ := b1e463291
           have i₂ := b1e59 y y
           grind)
        | exact superpose b1e59 b1e463291
        | exact resolve b1e463291 b1e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e463291
      have b1e463499 : (k y y) = (k y (τ y)) := by
        first
        | (have r₁ := b1e463459
           have r₂ := b1e463288
           grind)
        | exact resolve b1e463459 b1e463288
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e463288 b1e463459
      have b1e463518 : (M.op y y) = (k y (τ y)) := by
        first
        | (have i₁ := b1e463499
           have i₂ := b1e169192
           grind)
        | exact superpose b1e169192 b1e463499
        | exact resolve b1e463499 b1e169192
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e169192 b1e463499
      have b1e465997 : ∀ X0 X1 : G, (τ (k (σ y) y)) = (k y (τ (M.op X0 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e59 y (M.op X0 X1)
           have i₂ := b1e461608 X0 X1
           grind)
        | exact superpose b1e461608 b1e59
        | exact resolve b1e59 b1e461608
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e461608
      have b1e466015 : ∀ X0 X1 : G, (k y (τ y)) = (k y (τ (M.op X0 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e465997 X0 X1
           have i₂ := b1e59 y y
           grind)
        | exact superpose b1e59 b1e465997
        | exact resolve b1e465997 b1e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e59 b1e465997
      have b1e466067 : ∀ X0 X1 : G, (M.op y y) = (k y (τ (M.op X0 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e466015 X0 X1
           have i₂ := b1e463518
           grind)
        | exact superpose b1e463518 b1e466015
        | exact resolve b1e466015 b1e463518
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e463518 b1e466015
      have b1e466551 : (M.op y y) = (k y (τ (σ (M.op y y)))) := by
        first
        | (have i₁ := b1e466067 x (σ (M.op y y))
           have i₂ := b1e378282
           grind)
        | exact superpose b1e378282 b1e466067
        | exact resolve b1e466067 b1e378282
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e378282 b1e466067
      have b1e466631 : (M.op y y) = (k y (M.op y y)) := by
        first
        | (have i₁ := b1e466551
           have i₂ := b1e11 (M.op y y)
           grind)
        | exact superpose b1e11 b1e466551
        | exact resolve b1e466551 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e466551
      have b1e466901 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (M.op y (M.op y y)) := by
        first
        | (have i₁ := b1e1020 y (M.op y y)
           have i₂ := b1e466631
           grind)
        | exact superpose b1e466631 b1e1020
        | (have j0 := b1e1020 y (M.op y y)
           grind)
        | (have r₁ := b1e1020 y (M.op y y)
           have r₂ := b1e466631
           grind)
        | exact resolve b1e1020 b1e466631
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1020 b1e466631
      have b1e466911 : (M.op y y) = (M.op y (M.op y y)) := by grind
      clear b1e466901
      have b1e467010 : y = (M.op y (M.op (M.op y y) y)) := by
        first
        | (have i₁ := b1e971 y y
           have i₂ := b1e466911
           grind)
        | exact superpose b1e466911 b1e971
        | exact resolve b1e971 b1e466911
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e971 b1e466911
      have b1e467172 : y = (M.op y y) := by
        first
        | (have i₁ := b1e467010
           have i₂ := b1e10 y y y
           grind)
        | exact superpose b1e10 b1e467010
        | exact resolve b1e467010 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e467010
      have b1e467330 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e378280
           have i₂ := b1e467172
           grind)
        | exact superpose b1e467172 b1e378280
        | exact resolve b1e378280 b1e467172
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e378280 b1e467172
      have b1e467551 : False := by grind
      exact b1e467551
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X2 X0) X1)) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b2e17 : y ≠ (M.op x y) := by grind
      have b2e18 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e19 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e16
        | exact resolve b2e16 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
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
      have b2e21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X1 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e15
        | exact resolve b2e15 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e11 (k (τ X0) X1)
           have i₂ := b2e20 X0 X1
           grind)
        | exact superpose b2e20 b2e11
        | exact resolve b2e11 b2e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e26 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b2e10 (σ y) X0 (σ x)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X2 (M.op (M.op X0 X1) X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 (M.op (M.op X2 X0) X1) X3 X2
           have i₂ := b2e10 X0 X1 X2
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e28 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op X3 X2) X0) X1)) = (M.op X3 (M.op X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X2 (M.op (M.op (M.op X3 X2) X0) X1) X3
           have i₂ := b2e10 X0 X1 (M.op X3 X2)
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e11 (k X0 (τ X1))
           have i₂ := b2e21 X1 X0
           grind)
        | exact superpose b2e21 b2e11
        | exact resolve b2e11 b2e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e37 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e13 (σ x) (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e13
        | (have j0 := b2e13 (σ x) (σ y)
           grind)
        | (have r₁ := b2e13 (σ x) (σ y)
           have r₂ := b2e18
           grind)
        | exact resolve b2e13 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e38 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X0) X1) ∨ (k X2 (M.op (M.op X2 X0) X1)) = (M.op X2 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e13 X2 (M.op (M.op X2 X0) X1)
           have i₂ := b2e10 X0 X1 X2
           grind)
        | exact superpose b2e10 b2e13
        | (have j0 := b2e13 X2 (M.op (M.op X2 X0) X1)
           grind)
        | exact resolve b2e13 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e39 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
      clear b2e37
      have b2e40 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b2e39
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e39
        | exact resolve b2e39 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e39
      have b2e42 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ (k x y)) X0)) := by
        intro X0
        first
        | (have i₁ := b2e10 (σ x) X0 (σ x)
           have i₂ := b2e40
           grind)
        | exact superpose b2e40 b2e10
        | exact resolve b2e10 b2e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X0 X1
           have i₂ := b2e14 (σ X0) (σ X1)
           grind)
        | exact superpose b2e14 b2e15
        | (have j1 := b2e14 (σ X0) (σ X1)
           grind)
        | exact resolve b2e15 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e46 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e20 X0 X1
           have i₂ := b2e14 (τ X0) X1
           grind)
        | exact superpose b2e14 b2e20
        | (have j1 := b2e14 (τ X0) X1
           grind)
        | exact resolve b2e20 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e57 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ x) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e26 (M.op (M.op (σ y) X0) X1)
           have i₂ := b2e10 X0 X1 (σ y)
           grind)
        | exact superpose b2e10 b2e26
        | exact resolve b2e26 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e26
      have b2e80 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X4) = (M.op (M.op X0 X1) (M.op (M.op X2 X3) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e27 X2 X3 (M.op X0 X1) X4
           have i₂ := b2e27 X1 X2 X0 X3
           grind)
        | exact superpose b2e27 b2e27
        | exact resolve b2e27 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e83 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X2) X3))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X2 X3 (M.op X0 X1)
           have i₂ := b2e27 X1 X2 X0 X3
           grind)
        | exact superpose b2e27 b2e10
        | exact resolve b2e10 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e107 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (σ x) (σ x)) = (k (σ x) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e13 (σ x) (M.op X0 X1)
           have i₂ := b2e57 X0 X1
           grind)
        | exact superpose b2e57 b2e13
        | (have j0 := b2e13 (σ x) (M.op X0 X1)
           grind)
        | (have r₁ := b2e13 (σ x) (M.op X0 X1)
           have r₂ := b2e57 X0 X1
           grind)
        | exact resolve b2e13 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e109 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (k (σ x) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have j0 := b2e107 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e107
      have b2e110 : ∀ X0 X1 : G, (σ (k x y)) = (k (σ x) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e109 X0 X1
           have i₂ := b2e40
           grind)
        | exact superpose b2e40 b2e109
        | exact resolve b2e109 b2e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e109
      have b2e121 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X3)) = (M.op X1 (M.op X0 (M.op (M.op X1 X2) X3))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e28 X2 X3 X1 X0
           have i₂ := b2e27 X1 X2 X0 X3
           grind)
        | exact superpose b2e27 b2e28
        | exact resolve b2e28 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e129 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X3) X1) X2) X4) = (M.op X3 (M.op (M.op X0 (M.op X1 X2)) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e10 (M.op (M.op (M.op X0 X3) X1) X2) X4 X3
           have i₂ := b2e28 X1 X2 X3 X0
           grind)
        | exact superpose b2e28 b2e10
        | exact resolve b2e10 b2e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e130 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 X2)) X5) = (M.op X3 (M.op (M.op X4 (M.op (M.op (M.op X0 (M.op X3 X4)) X1) X2)) X5)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b2e27 X4 (M.op (M.op (M.op X0 (M.op X3 X4)) X1) X2) X3 X5
           have i₂ := b2e28 X1 X2 (M.op X3 X4) X0
           grind)
        | exact superpose b2e28 b2e27
        | exact resolve b2e27 b2e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e138 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 X2)) X5) = (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X3 X4))) (M.op (M.op X1 X2) X5))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b2e130 X0 X1 X2 X3 X4 X5
           have i₂ := b2e80 X4 (M.op X0 (M.op X3 X4)) X1 X2 X5
           grind)
        | exact superpose b2e80 b2e130
        | exact resolve b2e130 b2e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e130
      have b2e139 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 (M.op X1 X2)) X4)) = (M.op (M.op X0 X3) (M.op (M.op X1 X2) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e129 X0 X1 X2 X3 X4
           have i₂ := b2e27 X1 X2 (M.op X0 X3) X4
           grind)
        | exact superpose b2e27 b2e129
        | exact resolve b2e129 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e129
      have b2e198 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e13 (σ X0) (σ X1)
           have i₂ := b2e45 X0 X1
           grind)
        | exact superpose b2e45 b2e13
        | (have j0 := b2e13 (σ X0) (σ X1)
           have j1 := b2e45 X0 X1
           grind)
        | (have r₁ := b2e13 (σ X0) (σ X1)
           have r₂ := b2e45 X0 X1
           grind)
        | exact resolve b2e13 b2e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e199 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ X0) (M.op (σ (k X0 X1)) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 (σ X1) X2 (σ X0)
           have i₂ := b2e45 X0 X1
           grind)
        | exact superpose b2e45 b2e10
        | (have j1 := b2e45 X0 X1
           grind)
        | exact resolve b2e10 b2e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e200 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b2e45 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e45
      have b2e201 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b2e198 X0 X1
           have j1 := b2e13 (σ X0) (σ X1)
           grind)
        | (have r₁ := b2e198 X0 X1
           have r₂ := b2e13 (σ X0) (σ X1)
           grind)
        | exact resolve b2e198 b2e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e198
      have b2e206 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e201 X0 X1
           have i₂ := b2e15 X0 X1
           grind)
        | exact superpose b2e15 b2e201
        | (have j0 := b2e201 X0 X1
           grind)
        | exact resolve b2e201 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e201
      have b2e367 : ∀ X0 X1 : G, (τ (σ (k x y))) = (k x (τ (M.op X0 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e34 x (M.op X0 X1)
           have i₂ := b2e110 X0 X1
           grind)
        | exact superpose b2e110 b2e34
        | exact resolve b2e34 b2e110
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34 b2e110
      have b2e369 : ∀ X0 X1 : G, (k x y) = (k x (τ (M.op X0 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e367 X0 X1
           have i₂ := b2e11 (k x y)
           grind)
        | exact superpose b2e11 b2e367
        | exact resolve b2e367 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e367
      have b2e407 : (k x y) = (k x (τ (σ (k x y)))) := by
        first
        | (have i₁ := b2e369 (σ x) (σ x)
           have i₂ := b2e40
           grind)
        | exact superpose b2e40 b2e369
        | exact resolve b2e369 b2e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e40
      have b2e421 : (k x y) = (k x (k x y)) := by
        first
        | (have i₁ := b2e407
           have i₂ := b2e11 (k x y)
           grind)
        | exact superpose b2e11 b2e407
        | exact resolve b2e407 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e407
      have b2e441 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b2e421
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e421
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e421 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e443 : (k x y) = (M.op x (k x y)) ∨ (k x y) = (M.op x (k x y)) := by
        first
        | (have i₁ := b2e14 x (k x y)
           have i₂ := b2e421
           grind)
        | exact superpose b2e421 b2e14
        | (have j0 := b2e14 x (k x y)
           grind)
        | exact resolve b2e14 b2e421
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e421
      have b2e444 : (k x y) = (M.op x (k x y)) := by grind
      clear b2e443
      have b2e446 : (M.op x y) = (k x (M.op x y)) := by
        first
        | (have r₁ := b2e441
           have r₂ := b2e17
           grind)
        | exact resolve b2e441 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e441
      have b2e472 : (k x y) ≠ (k x y) ∨ (M.op x x) = (k x (k x y)) := by
        first
        | (have i₁ := b2e13 x (k x y)
           have i₂ := b2e444
           grind)
        | exact superpose b2e444 b2e13
        | (have j0 := b2e13 x (k x y)
           grind)
        | (have r₁ := b2e13 x (k x y)
           have r₂ := b2e444
           grind)
        | exact resolve b2e13 b2e444
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e474 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (k x y) (M.op (M.op (k x y) X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e28 X0 X1 (k x y) x
           have i₂ := b2e444
           grind)
        | exact superpose b2e444 b2e28
        | exact resolve b2e28 b2e444
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e478 : (k x y) = (k x (τ (k x y))) := by
        first
        | (have i₁ := b2e369 x (k x y)
           have i₂ := b2e444
           grind)
        | exact superpose b2e444 b2e369
        | exact resolve b2e369 b2e444
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e444
      have b2e480 : (M.op x x) = (k x (k x y)) := by grind
      clear b2e472
      have b2e481 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e474 X0 X1
           have i₂ := b2e10 X0 X1 (k x y)
           grind)
        | exact superpose b2e10 b2e474
        | exact resolve b2e474 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e474
      have b2e553 : (M.op x x) = (k x (M.op x y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b2e480
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e480
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e480 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e480
      have b2e558 : (M.op x x) = (k x (M.op x y)) := by
        first
        | (have r₁ := b2e553
           have r₂ := b2e17
           grind)
        | exact resolve b2e553 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e553
      have b2e559 : (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b2e558
           have i₂ := b2e446
           grind)
        | exact superpose b2e446 b2e558
        | exact resolve b2e558 b2e446
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e558
      have b2e592 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e83 X2 X2 X0 X1
           have i₂ := b2e10 X0 X1 X2
           grind)
        | exact superpose b2e10 b2e83
        | exact resolve b2e83 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e613 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 X3) (M.op X4 X5)) = (M.op (M.op X2 (M.op (M.op X3 X0) X1)) (M.op (M.op (M.op X0 X1) X4) X5)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b2e28 X4 X5 (M.op X2 (M.op (M.op X3 X0) X1)) (M.op X2 X3)
           have i₂ := b2e83 X2 X3 X0 X1
           grind)
        | exact superpose b2e83 b2e28
        | exact resolve b2e28 b2e83
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e83
      have b2e619 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 X3) (M.op X4 X5)) = (M.op (M.op (M.op X3 X0) X1) (M.op (M.op X2 (M.op (M.op X0 X1) X4)) X5)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b2e613 X0 X1 X2 X3 X4 X5
           have i₂ := b2e139 X2 (M.op X0 X1) X4 (M.op (M.op X3 X0) X1) X5
           grind)
        | (have i₁ := b2e613 X0 X1 X2 X3 (M.op X1 X2) X4
           have i₂ := b2e139 (M.op X0 X1) X1 X2 (M.op X2 (M.op (M.op X3 X0) X1)) X4
           grind)
        | exact superpose b2e139 b2e613
        | exact resolve b2e613 b2e139
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e613
      have b2e667 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 X3) (M.op X4 X5)) = (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 (M.op (M.op X0 X1) X4)) X5))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b2e619 X0 X1 X2 X3 X4 X5
           have i₂ := b2e27 X0 X1 X3 (M.op (M.op X2 (M.op (M.op X0 X1) X4)) X5)
           grind)
        | exact superpose b2e27 b2e619
        | exact resolve b2e619 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e619
      have b2e703 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 X3) (M.op X4 X5)) = (M.op X3 (M.op X1 (M.op (M.op X0 (M.op X2 (M.op (M.op X0 X1) X4))) X5))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b2e667 X0 X1 X2 X3 X4 X5
           have i₂ := b2e139 X0 X2 (M.op (M.op X0 X1) X4) X1 X5
           grind)
        | (have i₁ := b2e667 X0 X1 X0 X3 X2 X4
           have i₂ := b2e139 X0 (M.op X0 X1) X2 (M.op X0 X1) X4
           grind)
        | exact superpose b2e139 b2e667
        | exact resolve b2e667 b2e139
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e667
      have b2e720 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X2 X3) (M.op X4 X5)) = (M.op X3 (M.op X1 (M.op (M.op X2 (M.op X1 X4)) X5))) := by
        intro X1 X2 X3 X4 X5
        first
        | (have i₁ := b2e703 x X1 X2 X3 X4 X5
           have i₂ := b2e121 X2 x X1 X4
           grind)
        | exact superpose b2e121 b2e703
        | exact resolve b2e703 b2e121
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e703
      have b2e876 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op (M.op x y) X0)) := by
        intro X0
        first
        | (have i₁ := b2e10 x X0 x
           have i₂ := b2e559
           grind)
        | exact superpose b2e559 b2e10
        | exact resolve b2e10 b2e559
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e878 : ∀ X0 X1 : G, (M.op x (M.op (M.op x X0) X1)) = (M.op (M.op (M.op x y) X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e27 x X0 x X1
           have i₂ := b2e559
           grind)
        | exact superpose b2e559 b2e27
        | exact resolve b2e27 b2e559
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e889 : ∀ X0 X1 : G, (M.op x (M.op (M.op x X0) X1)) = (M.op x (M.op (M.op y X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e878 X0 X1
           have i₂ := b2e27 y X0 x X1
           grind)
        | exact superpose b2e27 b2e878
        | exact resolve b2e878 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e878
      have b2e891 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b2e876 X0
           have i₂ := b2e10 y X0 x
           grind)
        | exact superpose b2e10 b2e876
        | exact resolve b2e876 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e876
      have b2e895 : ∀ X0 X1 : G, (M.op x (M.op (M.op x X0) X1)) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e889 X0 X1
           have i₂ := b2e481 (M.op y X0) X1
           grind)
        | exact superpose b2e481 b2e889
        | exact resolve b2e889 b2e481
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e889
      have b2e900 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e895 X0 X1
           have i₂ := b2e10 X0 X1 x
           grind)
        | exact superpose b2e10 b2e895
        | exact resolve b2e895 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e895
      have b2e943 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op (M.op X0 X1) (M.op X2 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X1 (M.op (M.op X0 X2) X3) X0
           have i₂ := b2e121 (M.op X0 X1) X0 X2 X3
           grind)
        | exact superpose b2e121 b2e10
        | exact resolve b2e10 b2e121
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1122 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b2e559
           have i₂ := b2e891 x
           grind)
        | exact superpose b2e891 b2e559
        | exact resolve b2e559 b2e891
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e559
      have b2e1123 : (M.op y y) = (k x (M.op y y)) := by
        first
        | (have i₁ := b2e446
           have i₂ := b2e891 y
           grind)
        | exact superpose b2e891 b2e446
        | exact resolve b2e446 b2e891
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1124 : (σ y) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b2e19
           have i₂ := b2e891 y
           grind)
        | exact superpose b2e891 b2e19
        | exact resolve b2e19 b2e891
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19
      have b2e1125 : y ≠ (M.op y y) := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e891 y
           grind)
        | exact superpose b2e891 b2e17
        | exact resolve b2e17 b2e891
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1155 : (M.op y x) = (M.op y y) := by
        first
        | (have i₁ := b2e1122
           have i₂ := b2e891 y
           grind)
        | exact superpose b2e891 b2e1122
        | exact resolve b2e1122 b2e891
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1122
      have b2e1503 : ∀ X0 X1 : G, (σ (σ X1)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e200 (σ X0) (σ X1)
           have i₂ := b2e15 X0 X1
           grind)
        | exact superpose b2e15 b2e200
        | (have j0 := b2e200 (σ X0) (σ X1)
           grind)
        | exact resolve b2e200 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e200
      have b2e1569 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op x (M.op (M.op (M.op y y) X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e28 X0 X1 x y
           have i₂ := b2e1155
           grind)
        | exact superpose b2e1155 b2e28
        | exact resolve b2e28 b2e1155
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e28 b2e1155
      have b2e1582 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op (M.op y y) X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e1569 X0 X1
           have i₂ := b2e481 (M.op (M.op y y) X0) X1
           grind)
        | exact superpose b2e481 b2e1569
        | exact resolve b2e1569 b2e481
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1569
      have b2e1588 : ∀ X0 X1 : G, (M.op y (M.op (M.op y X0) X1)) = (M.op y (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e1582 X0 X1
           have i₂ := b2e27 y X0 y X1
           grind)
        | exact superpose b2e27 b2e1582
        | exact resolve b2e1582 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1582
      have b2e1593 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e1588 X0 X1
           have i₂ := b2e10 X0 X1 y
           grind)
        | exact superpose b2e10 b2e1588
        | exact resolve b2e1588 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1588
      have b2e1595 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e46 (σ X0) X1
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e46
        | exact resolve b2e46 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46
      have b2e1626 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e1595 X0 X1
           have i₂ := b2e15 X0 X1
           grind)
        | exact superpose b2e15 b2e1595
        | (have j0 := b2e1595 X0 X1
           grind)
        | exact resolve b2e1595 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1595
      have b2e1638 : (σ y) = (M.op x (σ y)) := by
        first
        | (have i₁ := b2e481 (σ x) (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e481
        | exact resolve b2e481 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e481
      have b2e1694 : (σ y) = (M.op y (σ y)) := by
        first
        | (have i₁ := b2e1638
           have i₂ := b2e891 (σ y)
           grind)
        | exact superpose b2e891 b2e1638
        | exact resolve b2e1638 b2e891
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1638
      have b2e1751 : (σ y) ≠ (σ y) ∨ (M.op y y) = (k y (σ y)) := by
        first
        | (have i₁ := b2e13 y (σ y)
           have i₂ := b2e1694
           grind)
        | exact superpose b2e1694 b2e13
        | (have j0 := b2e13 y (σ y)
           grind)
        | (have r₁ := b2e13 y (σ y)
           have r₂ := b2e1694
           grind)
        | exact resolve b2e13 b2e1694
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1764 : (M.op y y) = (k y (σ y)) := by grind
      clear b2e1751
      have b2e1812 : (τ (M.op y y)) = (k (τ y) y) := by
        first
        | (have i₁ := b2e25 y y
           have i₂ := b2e1764
           grind)
        | exact superpose b2e1764 b2e25
        | exact resolve b2e25 b2e1764
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1816 : ∀ X0 X1 : G, (σ (σ X1)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ (k X0 X1))) = (M.op (σ (σ X0)) (σ (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e206 (σ X0) (σ X1)
           have i₂ := b2e15 X0 X1
           grind)
        | exact superpose b2e15 b2e206
        | exact resolve b2e206 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1824 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e206 x (M.op x y)
           have i₂ := b2e446
           grind)
        | exact superpose b2e446 b2e206
        | exact resolve b2e206 b2e446
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e206 b2e446
      have b2e1835 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
      clear b2e1824
      have b2e1840 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b2e1835
           have i₂ := b2e891 y
           grind)
        | exact superpose b2e891 b2e1835
        | exact resolve b2e1835 b2e891
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1835
      have b2e1876 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op y y) = (k y (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e38 X0 X1 y
           have i₂ := b2e900 X0 X1
           grind)
        | exact superpose b2e900 b2e38
        | (have r₁ := b2e38 X0 X1 y
           have r₂ := b2e900 X0 X1
           grind)
        | exact resolve b2e38 b2e900
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e38
      have b2e1904 : ∀ X0 X1 : G, (M.op y y) = (k y (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have j0 := b2e1876 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1876
      have b2e1995 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X2 X3) X5)) = (M.op (M.op X4 (M.op X0 (M.op (M.op X1 X2) X3))) X5) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b2e80 X4 (M.op X0 X1) X2 X3 X5
           have i₂ := b2e27 X1 X2 X0 X3
           grind)
        | exact superpose b2e27 b2e80
        | exact resolve b2e80 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27 b2e80
      have b2e2131 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X0 (M.op (M.op X1 X2) X3))) X5) = (M.op (M.op X0 X1) (M.op (M.op X4 (M.op X2 X3)) X5)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b2e1995 X0 X1 X2 X3 X4 X5
           have i₂ := b2e139 X4 X2 X3 (M.op X0 X1) X5
           grind)
        | (have i₁ := b2e1995 X0 X1 X0 (M.op X1 X2) X4 X4
           have i₂ := b2e139 X0 X1 X2 (M.op X4 (M.op X0 X1)) X4
           grind)
        | exact superpose b2e139 b2e1995
        | exact resolve b2e1995 b2e139
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1995
      have b2e2217 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X0 (M.op (M.op X1 X2) X3))) X5) = (M.op X1 (M.op (M.op X0 (M.op X4 (M.op X2 X3))) X5)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b2e2131 X0 X1 X2 X3 X4 X5
           have i₂ := b2e139 X0 X4 (M.op X2 X3) X1 X5
           grind)
        | (have i₁ := b2e2131 X0 X1 X1 X2 X0 X4
           have i₂ := b2e139 X0 X1 X2 (M.op X0 X1) X4
           grind)
        | exact superpose b2e139 b2e2131
        | exact resolve b2e2131 b2e139
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2131
      have b2e3595 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 X1)) = (M.op X2 (M.op (M.op X3 (M.op y X0)) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e139 X3 y X0 X2 X1
           have i₂ := b2e900 X0 X1
           grind)
        | exact superpose b2e900 b2e139
        | exact resolve b2e139 b2e900
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e3722 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X2 (M.op (M.op X3 (M.op y X0)) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e3595 X0 X1 X2 X3
           have i₂ := b2e943 X3 X2 X0 X1
           grind)
        | exact superpose b2e943 b2e3595
        | exact resolve b2e3595 b2e943
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3595
      have b2e4700 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X2) = (M.op (σ X0) (M.op (k (σ X0) X1) X2)) ∨ (σ (τ X1)) = (M.op (σ X0) (σ (τ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e199 X0 (τ X1) X2
           have i₂ := b2e21 X1 X0
           grind)
        | exact superpose b2e21 b2e199
        | (have j0 := b2e199 X0 (τ X1) X2
           grind)
        | exact resolve b2e199 b2e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21 b2e199
      have b2e4765 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (σ X0) (M.op (k (σ X0) X1) X2)) ∨ (σ (τ X1)) = (M.op (σ X0) (σ (τ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e4700 X0 X1 X2
           have i₂ := b2e12 X1
           grind)
        | exact superpose b2e12 b2e4700
        | (have j0 := b2e4700 X0 X1 X2
           grind)
        | exact resolve b2e4700 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4700
      have b2e4789 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (σ X0) (M.op (k (σ X0) X1) X2)) ∨ (M.op (σ X0) X1) = X1 := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e4765 X0 X0 X2
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e4765
        | (have j0 := b2e4765 X0 X1 X2
           grind)
        | exact resolve b2e4765 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4765
      have b2e4966 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X5 (M.op (M.op X6 (M.op X2 (M.op X5 X6))) (M.op X0 X1))) = (M.op (M.op X2 (M.op X3 X4)) (M.op (M.op (M.op X3 X4) X0) X1)) := by
        intro X0 X1 X2 X3 X4 X5 X6
        first
        | (have i₁ := b2e138 X2 X3 X4 X5 X6 (M.op (M.op (M.op X3 X4) X0) X1)
           have i₂ := b2e10 X0 X1 (M.op X3 X4)
           grind)
        | exact superpose b2e10 b2e138
        | exact resolve b2e138 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e5013 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op (M.op X4 (M.op X0 (M.op X1 X4))) (M.op X2 X3)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e121 (M.op X4 (M.op X0 (M.op X1 X4))) X1 X2 X3
           have i₂ := b2e138 X0 X1 X2 X1 X4 X3
           grind)
        | exact superpose b2e138 b2e121
        | exact resolve b2e121 b2e138
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e121 b2e138
      have b2e5121 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op (M.op X0 (M.op X1 X4)) (M.op (M.op X4 X2) X3)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e5013 X0 X1 X2 X3 X4
           have i₂ := b2e943 X4 (M.op X0 (M.op X1 X4)) X2 X3
           grind)
        | exact superpose b2e943 b2e5013
        | exact resolve b2e5013 b2e943
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e5013
      have b2e5165 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X5 (M.op (M.op X6 (M.op X2 (M.op X5 X6))) (M.op X0 X1))) = (M.op (M.op X3 X4) (M.op (M.op X2 (M.op (M.op X3 X4) X0)) X1)) := by
        intro X0 X1 X2 X3 X4 X5 X6
        first
        | (have i₁ := b2e4966 X0 X1 X2 X3 X4 X5 X6
           have i₂ := b2e139 X2 (M.op X3 X4) X0 (M.op X3 X4) X1
           grind)
        | (have i₁ := b2e4966 (M.op X1 X2) X4 X2 X3 X4 X5 X6
           have i₂ := b2e139 (M.op X3 X4) X1 X2 (M.op X2 (M.op X3 X4)) X4
           grind)
        | exact superpose b2e139 b2e4966
        | exact resolve b2e4966 b2e139
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4966
      have b2e5304 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op (M.op X1 X4) (M.op (M.op X0 (M.op X4 X2)) X3)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e5121 X0 X1 X2 X3 X4
           have i₂ := b2e139 X0 X4 X2 (M.op X1 X4) X3
           grind)
        | (have i₁ := b2e5121 X0 X1 (M.op X1 X2) X4 X0
           have i₂ := b2e139 X0 X1 X2 (M.op X0 (M.op X1 X0)) X4
           grind)
        | exact superpose b2e139 b2e5121
        | exact resolve b2e5121 b2e139
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e5121
      have b2e5342 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X5 (M.op (M.op X6 (M.op X2 (M.op X5 X6))) (M.op X0 X1))) = (M.op X4 (M.op (M.op X3 (M.op X2 (M.op (M.op X3 X4) X0))) X1)) := by
        intro X0 X1 X2 X3 X4 X5 X6
        first
        | (have i₁ := b2e5165 X0 X1 X2 X3 X4 X5 X6
           have i₂ := b2e139 X3 X2 (M.op (M.op X3 X4) X0) X4 X1
           grind)
        | (have i₁ := b2e5165 X2 X4 X0 X3 X4 X5 X6
           have i₂ := b2e139 X0 (M.op X3 X4) X2 (M.op X3 X4) X4
           grind)
        | exact superpose b2e139 b2e5165
        | exact resolve b2e5165 b2e139
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e5165
      have b2e5473 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X4 (M.op (M.op X1 (M.op X0 (M.op X4 X2))) X3)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e5304 X0 X1 X2 X3 X4
           have i₂ := b2e139 X1 X0 (M.op X4 X2) X4 X3
           grind)
        | (have i₁ := b2e5304 X0 X1 X2 X4 X1
           have i₂ := b2e139 X0 X1 X2 (M.op X1 X1) X4
           grind)
        | exact superpose b2e139 b2e5304
        | exact resolve b2e5304 b2e139
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e5304
      have b2e5507 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X5 (M.op (M.op X6 (M.op X2 (M.op X5 X6))) (M.op X0 X1))) = (M.op X4 (M.op X3 (M.op (M.op X2 (M.op X3 (M.op X4 X0))) X1))) := by
        intro X0 X1 X2 X3 X4 X5 X6
        first
        | (have i₁ := b2e5342 X0 X1 X2 X3 X4 X5 X6
           have i₂ := b2e2217 X2 X3 X4 X0 X3 X1
           grind)
        | exact superpose b2e2217 b2e5342
        | exact resolve b2e5342 b2e2217
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2217 b2e5342
      have b2e5642 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op X5 (M.op (M.op X6 (M.op X2 (M.op X5 X6))) (M.op X0 X1))) = (M.op (M.op X2 X4) (M.op (M.op X4 X0) X1)) := by
        intro X0 X1 X2 X4 X5 X6
        first
        | (have i₁ := b2e5507 X0 X1 X2 x X4 X5 X6
           have i₂ := b2e720 x X2 X4 (M.op X4 X0) X1
           grind)
        | (have i₁ := b2e5507 X0 X1 X2 X4 (M.op X2 x) X5 X6
           have i₂ := b2e720 X1 X2 x X4 (M.op (M.op X2 (M.op X4 (M.op (M.op X2 x) X0))) X1)
           grind)
        | exact superpose b2e720 b2e5507
        | exact resolve b2e5507 b2e720
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e720 b2e5507
      have b2e5758 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op X4 (M.op (M.op X2 (M.op X4 X0)) X1)) = (M.op X5 (M.op (M.op X6 (M.op X2 (M.op X5 X6))) (M.op X0 X1))) := by
        intro X0 X1 X2 X4 X5 X6
        first
        | (have i₁ := b2e5642 X0 X1 X2 X4 X5 X6
           have i₂ := b2e139 X2 X4 X0 X4 X1
           grind)
        | (have i₁ := b2e5642 (M.op X1 X2) X4 X2 X0 X5 X6
           have i₂ := b2e139 X0 X1 X2 (M.op X2 X0) X4
           grind)
        | exact superpose b2e139 b2e5642
        | exact resolve b2e5642 b2e139
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e5642
      have b2e5842 : ∀ X0 X1 X2 X4 X6 : G, (M.op X4 (M.op (M.op X2 (M.op X4 X0)) X1)) = (M.op (M.op X2 (M.op X6 X6)) (M.op X0 X1)) := by
        intro X0 X1 X2 X4 X6
        first
        | (have i₁ := b2e5758 X0 X1 X2 X4 x X6
           have i₂ := b2e5473 X2 X6 X6 (M.op X0 X1) x
           grind)
        | exact superpose b2e5473 b2e5758
        | exact resolve b2e5758 b2e5473
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e5473 b2e5758
      have b2e5910 : ∀ X0 X1 X2 X4 X6 : G, (M.op X4 (M.op (M.op X2 (M.op X4 X0)) X1)) = (M.op (M.op X6 X6) (M.op (M.op X2 X0) X1)) := by
        intro X0 X1 X2 X4 X6
        first
        | (have i₁ := b2e5842 X0 X1 X2 X4 X6
           have i₂ := b2e943 X2 (M.op X6 X6) X0 X1
           grind)
        | exact superpose b2e943 b2e5842
        | exact resolve b2e5842 b2e943
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e5842
      have b2e5970 : ∀ X0 X1 X2 X4 X6 : G, (M.op X4 (M.op (M.op X2 (M.op X4 X0)) X1)) = (M.op X6 (M.op (M.op X6 (M.op X2 X0)) X1)) := by
        intro X0 X1 X2 X4 X6
        first
        | (have i₁ := b2e5910 X0 X1 X2 X4 X6
           have i₂ := b2e139 X6 X2 X0 X6 X1
           grind)
        | (have i₁ := b2e5910 (M.op X1 X2) X4 X0 X4 X6
           have i₂ := b2e139 X0 X1 X2 (M.op X6 X6) X4
           grind)
        | exact superpose b2e139 b2e5910
        | exact resolve b2e5910 b2e139
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e139 b2e5910
      have b2e6010 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X2 X0) X1) = (M.op X4 (M.op (M.op X2 (M.op X4 X0)) X1)) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b2e5970 X0 X1 X2 X4 x
           have i₂ := b2e10 (M.op X2 X0) X1 x
           grind)
        | exact superpose b2e10 b2e5970
        | exact resolve b2e5970 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e5970
      have b2e9254 : (M.op x y) = (k x (τ (M.op x y))) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b2e478
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e478
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e478 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e478
      have b2e9271 : (M.op x y) = (k x (τ (M.op x y))) := by
        first
        | (have r₁ := b2e9254
           have r₂ := b2e17
           grind)
        | exact resolve b2e9254 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e9254
      have b2e9280 : (M.op x y) = (k x y) := by
        first
        | (have i₁ := b2e9271
           have i₂ := b2e369 x y
           grind)
        | exact superpose b2e369 b2e9271
        | exact resolve b2e9271 b2e369
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e369 b2e9271
      have b2e9288 : (k x y) = (M.op y y) := by
        first
        | (have i₁ := b2e9280
           have i₂ := b2e891 y
           grind)
        | exact superpose b2e891 b2e9280
        | exact resolve b2e9280 b2e891
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e891 b2e9280
      have b2e9393 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ (M.op y y)) X0)) := by
        intro X0
        first
        | (have i₁ := b2e42 X0
           have i₂ := b2e9288
           grind)
        | exact superpose b2e9288 b2e42
        | exact resolve b2e42 b2e9288
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e42 b2e9288
      have b2e9414 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y y)) X0) := by
        intro X0
        first
        | (have i₁ := b2e9393 X0
           have i₂ := b2e57 (σ (M.op y y)) X0
           grind)
        | exact superpose b2e57 b2e9393
        | exact resolve b2e9393 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e9393
      have b2e11801 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b2e592 y (σ y) x
           have i₂ := b2e1694
           grind)
        | exact superpose b2e1694 b2e592
        | exact resolve b2e592 b2e1694
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e592
      have b2e12186 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b2e13 (M.op X0 X0) (σ y)
           have i₂ := b2e11801 X0
           grind)
        | exact superpose b2e11801 b2e13
        | (have j0 := b2e13 (M.op X0 X0) (σ y)
           grind)
        | (have r₁ := b2e13 (M.op X0 X0) (σ y)
           have r₂ := b2e11801 X0
           grind)
        | exact resolve b2e13 b2e11801
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e11801
      have b2e12219 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (σ y)) := by
        intro X0
        first
        | (have j0 := b2e12186 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e12186
      have b2e12239 : ∀ X0 : G, (k (M.op X0 X0) (σ y)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
        intro X0
        first
        | (have i₁ := b2e12219 X0
           have i₂ := b2e943 X0 X0 X0 X0
           grind)
        | exact superpose b2e943 b2e12219
        | exact resolve b2e12219 b2e943
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e943 b2e12219
      have b2e12280 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b2e12239 X0
           have i₂ := b2e10 X0 X0 X0
           grind)
        | exact superpose b2e10 b2e12239
        | exact resolve b2e12239 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e12239
      have b2e12439 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) y) := by
        intro X0
        first
        | (have i₁ := b2e25 (M.op X0 X0) y
           have i₂ := b2e12280 X0
           grind)
        | exact superpose b2e12280 b2e25
        | exact resolve b2e25 b2e12280
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e12280
      have b2e82367 : (σ (σ (M.op y y))) ≠ (σ (σ (M.op y y))) ∨ (σ (σ (M.op y y))) = (M.op (σ (σ x)) (σ (σ x))) := by
        first
        | (have i₁ := b2e1816 x (M.op y y)
           have i₂ := b2e1123
           grind)
        | exact superpose b2e1123 b2e1816
        | exact resolve b2e1816 b2e1123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1123
      have b2e82425 : (σ (σ (M.op y y))) = (M.op (σ (σ x)) (σ (σ x))) := by grind
      clear b2e82367
      have b2e82719 : (τ (σ (σ (M.op y y)))) = (k (τ (σ (σ (M.op y y)))) y) := by
        first
        | (have i₁ := b2e12439 (σ (σ x))
           have i₂ := b2e82425
           grind)
        | exact superpose b2e82425 b2e12439
        | exact resolve b2e12439 b2e82425
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e12439
      have b2e82776 : (M.op y y) = (k y (σ (σ (M.op y y)))) := by
        first
        | (have i₁ := b2e1904 (σ (σ x)) (σ (σ x))
           have i₂ := b2e82425
           grind)
        | exact superpose b2e82425 b2e1904
        | exact resolve b2e1904 b2e82425
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1904 b2e82425
      have b2e82827 : (σ (M.op y y)) = (k (σ (M.op y y)) y) := by
        first
        | (have i₁ := b2e82719
           have i₂ := b2e11 (σ (M.op y y))
           grind)
        | exact superpose b2e11 b2e82719
        | exact resolve b2e82719 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e82719
      have b2e92516 : (τ (M.op y y)) = (k (τ y) (σ (M.op y y))) := by
        first
        | (have i₁ := b2e25 y (σ (M.op y y))
           have i₂ := b2e82776
           grind)
        | exact superpose b2e82776 b2e25
        | exact resolve b2e25 b2e82776
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e25 b2e82776
      have b2e92536 : (k (τ y) y) = (k (τ y) (σ (M.op y y))) := by
        first
        | (have i₁ := b2e92516
           have i₂ := b2e1812
           grind)
        | exact superpose b2e1812 b2e92516
        | exact resolve b2e92516 b2e1812
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1812 b2e92516
      have b2e92708 : ∀ X0 : G, (M.op y X0) = (M.op (σ (M.op y y)) (M.op (σ (M.op y y)) X0)) ∨ y = (M.op (σ (M.op y y)) y) := by
        intro X0
        first
        | (have i₁ := b2e4789 (M.op y y) y X0
           have i₂ := b2e82827
           grind)
        | exact superpose b2e82827 b2e4789
        | (have j0 := b2e4789 (M.op y y) y x
           grind)
        | exact resolve b2e4789 b2e82827
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4789
      have b2e92727 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) (M.op (σ (M.op y y)) X0)) ∨ y = (M.op (σ (M.op y y)) y) := by
        intro X0
        first
        | (have i₁ := b2e92708 X0
           have i₂ := b2e9414 (M.op (σ (M.op y y)) X0)
           grind)
        | exact superpose b2e9414 b2e92708
        | exact resolve b2e92708 b2e9414
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e92708
      have b2e92739 : ∀ X0 : G, (M.op y X0) = (M.op (σ (M.op y y)) X0) ∨ y = (M.op (σ (M.op y y)) y) := by
        intro X0
        first
        | (have i₁ := b2e92727 X0
           have i₂ := b2e57 (σ (M.op y y)) X0
           grind)
        | exact superpose b2e57 b2e92727
        | exact resolve b2e92727 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e57 b2e92727
      have b2e92742 : ∀ X0 : G, (M.op (σ x) X0) = (M.op y X0) ∨ y = (M.op (σ (M.op y y)) y) := by
        intro X0
        first
        | (have i₁ := b2e92739 X0
           have i₂ := b2e9414 X0
           grind)
        | exact superpose b2e9414 b2e92739
        | exact resolve b2e92739 b2e9414
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e92739
      have b2e92743 : ∀ X0 : G, y = (M.op (σ x) y) ∨ (M.op (σ x) X0) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b2e92742 X0
           have i₂ := b2e9414 y
           grind)
        | exact superpose b2e9414 b2e92742
        | (have j0 := b2e92742 X0
           grind)
        | exact resolve b2e92742 b2e9414
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e9414 b2e92742
      have b2e167695 : ∀ X0 : G, y = (M.op y y) ∨ (M.op (σ x) X0) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b2e1593 (σ x) y
           have i₂ := b2e92743 X0
           grind)
        | exact superpose b2e92743 b2e1593
        | (have j1 := b2e92743 X0
           grind)
        | exact resolve b2e1593 b2e92743
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1593 b2e92743
      have b2e168289 : ∀ X0 : G, (M.op (σ x) X0) = (M.op y X0) := by
        intro X0
        first
        | (have j0 := b2e167695 X0
           grind)
        | (have r₁ := b2e167695 X0
           have r₂ := b2e1125
           grind)
        | exact resolve b2e167695 b2e1125
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e167695
      have b2e174101 : (σ (M.op y y)) = (M.op y (σ x)) := by
        first
        | (have i₁ := b2e1840
           have i₂ := b2e168289 (σ x)
           grind)
        | exact superpose b2e168289 b2e1840
        | exact resolve b2e1840 b2e168289
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1840
      have b2e175752 : (σ y) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b2e1124
           have i₂ := b2e174101
           grind)
        | exact superpose b2e174101 b2e1124
        | exact resolve b2e1124 b2e174101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1124
      have b2e175773 : (M.op y (σ x)) = (k (M.op y (σ x)) y) := by
        first
        | (have i₁ := b2e82827
           have i₂ := b2e174101
           grind)
        | exact superpose b2e174101 b2e82827
        | exact resolve b2e82827 b2e174101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e82827
      have b2e175776 : (k (τ y) y) = (k (τ y) (M.op y (σ x))) := by
        first
        | (have i₁ := b2e92536
           have i₂ := b2e174101
           grind)
        | exact superpose b2e174101 b2e92536
        | exact resolve b2e92536 b2e174101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e92536
      have b2e180156 : (M.op y (σ x)) = (M.op (M.op y (σ x)) y) ∨ y = (M.op (M.op y (σ x)) y) := by
        first
        | (have i₁ := b2e14 (M.op y (σ x)) y
           have i₂ := b2e175773
           grind)
        | exact superpose b2e175773 b2e14
        | (have j0 := b2e14 (M.op y (σ x)) y
           grind)
        | exact resolve b2e14 b2e175773
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e180163 : (σ (M.op y (σ x))) = (σ (M.op (M.op y (σ x)) y)) ∨ y = (M.op (M.op y (σ x)) y) := by
        first
        | (have i₁ := b2e1626 (M.op y (σ x)) y
           have i₂ := b2e175773
           grind)
        | exact superpose b2e175773 b2e1626
        | (have j0 := b2e1626 (M.op y (σ x)) y
           grind)
        | exact resolve b2e1626 b2e175773
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1626 b2e175773
      have b2e180168 : (σ (M.op y (σ x))) = (σ (M.op (σ x) y)) ∨ y = (M.op (M.op y (σ x)) y) := by
        first
        | (have i₁ := b2e180163
           have i₂ := b2e900 (σ x) y
           grind)
        | exact superpose b2e900 b2e180163
        | exact resolve b2e180163 b2e900
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e180163
      have b2e180169 : (M.op y (σ x)) = (M.op (σ x) y) ∨ y = (M.op (M.op y (σ x)) y) := by
        first
        | (have i₁ := b2e180156
           have i₂ := b2e900 (σ x) y
           grind)
        | exact superpose b2e900 b2e180156
        | exact resolve b2e180156 b2e900
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e180156
      have b2e180172 : (σ (M.op y y)) = (σ (M.op y (σ x))) ∨ y = (M.op (M.op y (σ x)) y) := by
        first
        | (have i₁ := b2e180168
           have i₂ := b2e168289 y
           grind)
        | exact superpose b2e168289 b2e180168
        | exact resolve b2e180168 b2e168289
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e180168
      have b2e180173 : (M.op y y) = (M.op y (σ x)) ∨ y = (M.op (M.op y (σ x)) y) := by
        first
        | (have i₁ := b2e180169
           have i₂ := b2e168289 y
           grind)
        | exact superpose b2e168289 b2e180169
        | exact resolve b2e180169 b2e168289
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e180169
      have b2e180176 : (M.op y (σ x)) = (σ (M.op y (σ x))) ∨ y = (M.op (M.op y (σ x)) y) := by
        first
        | (have i₁ := b2e180172
           have i₂ := b2e174101
           grind)
        | exact superpose b2e174101 b2e180172
        | exact resolve b2e180172 b2e174101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e180172
      have b2e180177 : y = (M.op (σ x) y) ∨ (M.op y y) = (M.op y (σ x)) := by
        first
        | (have i₁ := b2e180173
           have i₂ := b2e900 (σ x) y
           grind)
        | exact superpose b2e900 b2e180173
        | exact resolve b2e180173 b2e900
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e180173
      have b2e180180 : y = (M.op (σ x) y) ∨ (M.op y (σ x)) = (σ (M.op y (σ x))) := by
        first
        | (have i₁ := b2e180176
           have i₂ := b2e900 (σ x) y
           grind)
        | exact superpose b2e900 b2e180176
        | exact resolve b2e180176 b2e900
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e180176
      have b2e180181 : y = (M.op y y) ∨ (M.op y y) = (M.op y (σ x)) := by
        first
        | (have i₁ := b2e180177
           have i₂ := b2e168289 y
           grind)
        | exact superpose b2e168289 b2e180177
        | exact resolve b2e180177 b2e168289
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e180177
      have b2e180184 : y = (M.op y y) ∨ (M.op y (σ x)) = (σ (M.op y (σ x))) := by
        first
        | (have i₁ := b2e180180
           have i₂ := b2e168289 y
           grind)
        | exact superpose b2e168289 b2e180180
        | exact resolve b2e180180 b2e168289
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e168289 b2e180180
      have b2e180185 : (M.op y y) = (M.op y (σ x)) := by
        first
        | (have r₁ := b2e180181
           have r₂ := b2e1125
           grind)
        | exact resolve b2e180181 b2e1125
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e180181
      have b2e180188 : (M.op y (σ x)) = (σ (M.op y (σ x))) := by
        first
        | (have r₁ := b2e180184
           have r₂ := b2e1125
           grind)
        | exact resolve b2e180184 b2e1125
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1125 b2e180184
      have b2e180190 : (M.op y y) = (σ (M.op y y)) := by
        first
        | (have i₁ := b2e180188
           have i₂ := b2e180185
           grind)
        | exact superpose b2e180185 b2e180188
        | exact resolve b2e180188 b2e180185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e180188
      have b2e181080 : (σ y) ≠ (M.op y y) := by
        first
        | (have i₁ := b2e175752
           have i₂ := b2e180185
           grind)
        | exact superpose b2e180185 b2e175752
        | exact resolve b2e175752 b2e180185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e175752
      have b2e197090 : (σ (σ (k (τ y) y))) ≠ (σ (σ (M.op y (σ x)))) ∨ (σ (σ (M.op y (σ x)))) = (M.op (σ (σ (τ y))) (σ (σ (M.op y (σ x))))) := by
        first
        | (have i₁ := b2e1503 (τ y) (M.op y (σ x))
           have i₂ := b2e175776
           grind)
        | exact superpose b2e175776 b2e1503
        | (have j0 := b2e1503 (τ y) (M.op y (σ x))
           grind)
        | exact resolve b2e1503 b2e175776
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1503
      have b2e197093 : (σ (σ (k (τ y) y))) ≠ (σ (σ (M.op y (σ x)))) ∨ (σ (σ (k (τ y) y))) = (M.op (σ (σ (τ y))) (σ (σ (τ y)))) := by
        first
        | (have i₁ := b2e1816 (τ y) (M.op y (σ x))
           have i₂ := b2e175776
           grind)
        | exact superpose b2e175776 b2e1816
        | (have j0 := b2e1816 (τ y) y
           grind)
        | exact resolve b2e1816 b2e175776
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1816 b2e175776
      have b2e197098 : (σ (σ (M.op y y))) ≠ (σ (σ (k (τ y) y))) ∨ (σ (σ (k (τ y) y))) = (M.op (σ (σ (τ y))) (σ (σ (τ y)))) := by
        first
        | (have i₁ := b2e197093
           have i₂ := b2e180185
           grind)
        | exact superpose b2e180185 b2e197093
        | exact resolve b2e197093 b2e180185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197093
      have b2e197101 : (σ (σ (M.op y y))) ≠ (σ (σ (k (τ y) y))) ∨ (σ (σ (M.op y (σ x)))) = (M.op (σ (σ (τ y))) (σ (σ (M.op y (σ x))))) := by
        first
        | (have i₁ := b2e197090
           have i₂ := b2e180185
           grind)
        | exact superpose b2e180185 b2e197090
        | exact resolve b2e197090 b2e180185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197090
      have b2e197125 : (σ (σ (M.op y y))) ≠ (σ (k y (σ y))) ∨ (σ (σ (k (τ y) y))) = (M.op (σ (σ (τ y))) (σ (σ (τ y)))) := by
        first
        | (have i₁ := b2e197098
           have i₂ := b2e20 y y
           grind)
        | exact superpose b2e20 b2e197098
        | exact resolve b2e197098 b2e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197098
      have b2e197128 : (σ (σ (M.op y y))) ≠ (σ (k y (σ y))) ∨ (σ (σ (M.op y (σ x)))) = (M.op (σ (σ (τ y))) (σ (σ (M.op y (σ x))))) := by
        first
        | (have i₁ := b2e197101
           have i₂ := b2e20 y y
           grind)
        | exact superpose b2e20 b2e197101
        | exact resolve b2e197101 b2e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197101
      have b2e197152 : (σ (M.op y y)) ≠ (σ (σ (M.op y y))) ∨ (σ (σ (k (τ y) y))) = (M.op (σ (σ (τ y))) (σ (σ (τ y)))) := by
        first
        | (have i₁ := b2e197125
           have i₂ := b2e1764
           grind)
        | exact superpose b2e1764 b2e197125
        | exact resolve b2e197125 b2e1764
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197125
      have b2e197155 : (σ (M.op y y)) ≠ (σ (σ (M.op y y))) ∨ (σ (σ (M.op y (σ x)))) = (M.op (σ (σ (τ y))) (σ (σ (M.op y (σ x))))) := by
        first
        | (have i₁ := b2e197128
           have i₂ := b2e1764
           grind)
        | exact superpose b2e1764 b2e197128
        | exact resolve b2e197128 b2e1764
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197128
      have b2e197172 : (M.op y (σ x)) ≠ (σ (M.op y (σ x))) ∨ (σ (σ (k (τ y) y))) = (M.op (σ (σ (τ y))) (σ (σ (τ y)))) := by
        first
        | (have i₁ := b2e197152
           have i₂ := b2e174101
           grind)
        | exact superpose b2e174101 b2e197152
        | exact resolve b2e197152 b2e174101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197152
      have b2e197174 : (M.op y (σ x)) ≠ (σ (M.op y (σ x))) ∨ (σ (σ (M.op y (σ x)))) = (M.op (σ (σ (τ y))) (σ (σ (M.op y (σ x))))) := by
        first
        | (have i₁ := b2e197155
           have i₂ := b2e174101
           grind)
        | exact superpose b2e174101 b2e197155
        | exact resolve b2e197155 b2e174101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197155
      have b2e197180 : (M.op y y) ≠ (σ (M.op y y)) ∨ (σ (σ (k (τ y) y))) = (M.op (σ (σ (τ y))) (σ (σ (τ y)))) := by
        first
        | (have i₁ := b2e197172
           have i₂ := b2e180185
           grind)
        | exact superpose b2e180185 b2e197172
        | exact resolve b2e197172 b2e180185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197172
      have b2e197181 : (M.op y y) ≠ (σ (M.op y y)) ∨ (σ (σ (M.op y (σ x)))) = (M.op (σ (σ (τ y))) (σ (σ (M.op y (σ x))))) := by
        first
        | (have i₁ := b2e197174
           have i₂ := b2e180185
           grind)
        | exact superpose b2e180185 b2e197174
        | exact resolve b2e197174 b2e180185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197174
      have b2e197186 : (σ (σ (k (τ y) y))) = (M.op (σ (σ (τ y))) (σ (σ (τ y)))) := by
        first
        | (have r₁ := b2e197180
           have r₂ := b2e180190
           grind)
        | exact resolve b2e197180 b2e180190
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197180
      have b2e197187 : (σ (σ (M.op y (σ x)))) = (M.op (σ (σ (τ y))) (σ (σ (M.op y (σ x))))) := by
        first
        | (have r₁ := b2e197181
           have r₂ := b2e180190
           grind)
        | exact resolve b2e197181 b2e180190
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e180190 b2e197181
      have b2e197191 : (M.op (σ y) (σ y)) = (σ (σ (k (τ y) y))) := by
        first
        | (have i₁ := b2e197186
           have i₂ := b2e12 y
           grind)
        | exact superpose b2e12 b2e197186
        | exact resolve b2e197186 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197186
      have b2e197192 : (σ (σ (M.op y y))) = (M.op (σ (σ (τ y))) (σ (σ (M.op y y)))) := by
        first
        | (have i₁ := b2e197187
           have i₂ := b2e180185
           grind)
        | exact superpose b2e180185 b2e197187
        | exact resolve b2e197187 b2e180185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197187
      have b2e197194 : (σ (k y (σ y))) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b2e197191
           have i₂ := b2e20 y y
           grind)
        | exact superpose b2e20 b2e197191
        | exact resolve b2e197191 b2e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e20 b2e197191
      have b2e197195 : (σ (M.op y (σ x))) = (M.op (σ (σ (τ y))) (σ (M.op y (σ x)))) := by
        first
        | (have i₁ := b2e197192
           have i₂ := b2e174101
           grind)
        | exact superpose b2e174101 b2e197192
        | exact resolve b2e197192 b2e174101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197192
      have b2e197197 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b2e197194
           have i₂ := b2e1764
           grind)
        | exact superpose b2e1764 b2e197194
        | exact resolve b2e197194 b2e1764
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1764 b2e197194
      have b2e197198 : (σ (M.op y y)) = (M.op (σ (σ (τ y))) (σ (M.op y y))) := by
        first
        | (have i₁ := b2e197195
           have i₂ := b2e180185
           grind)
        | exact superpose b2e180185 b2e197195
        | exact resolve b2e197195 b2e180185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197195
      have b2e197199 : (M.op (σ y) (σ y)) = (M.op y (σ x)) := by
        first
        | (have i₁ := b2e197197
           have i₂ := b2e174101
           grind)
        | exact superpose b2e174101 b2e197197
        | exact resolve b2e197197 b2e174101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197197
      have b2e197200 : (M.op y (σ x)) = (M.op (σ (σ (τ y))) (M.op y (σ x))) := by
        first
        | (have i₁ := b2e197198
           have i₂ := b2e174101
           grind)
        | exact superpose b2e174101 b2e197198
        | exact resolve b2e197198 b2e174101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e174101 b2e197198
      have b2e197201 : (M.op y y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b2e197199
           have i₂ := b2e180185
           grind)
        | exact superpose b2e180185 b2e197199
        | exact resolve b2e197199 b2e180185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197199
      have b2e197202 : (M.op y y) = (M.op (σ (σ (τ y))) (M.op y y)) := by
        first
        | (have i₁ := b2e197200
           have i₂ := b2e180185
           grind)
        | exact superpose b2e180185 b2e197200
        | exact resolve b2e197200 b2e180185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e180185 b2e197200
      have b2e197203 : (M.op y y) = (M.op (σ y) (M.op y y)) := by
        first
        | (have i₁ := b2e197202
           have i₂ := b2e12 y
           grind)
        | exact superpose b2e12 b2e197202
        | exact resolve b2e197202 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197202
      have b2e197590 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (σ y) (M.op (M.op X0 (M.op y y)) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e6010 (σ y) X1 X0 (σ y)
           have i₂ := b2e197201
           grind)
        | exact superpose b2e197201 b2e6010
        | exact resolve b2e6010 b2e197201
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e6010
      have b2e197616 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (σ y) (M.op (M.op X0 y) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e197590 X0 X1
           have i₂ := b2e3722 y X1 (σ y) X0
           grind)
        | exact superpose b2e3722 b2e197590
        | exact resolve b2e197590 b2e3722
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3722 b2e197590
      have b2e203585 : ∀ X0 : G, (M.op (M.op y y) X0) = (M.op (σ y) (M.op (M.op y y) X0)) := by
        intro X0
        first
        | (have i₁ := b2e10 (M.op y y) X0 (σ y)
           have i₂ := b2e197203
           grind)
        | exact superpose b2e197203 b2e10
        | exact resolve b2e10 b2e197203
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197203
      have b2e203731 : ∀ X0 : G, (M.op (M.op y y) X0) = (M.op (M.op y (σ y)) X0) := by
        intro X0
        first
        | (have i₁ := b2e203585 X0
           have i₂ := b2e197616 y X0
           grind)
        | exact superpose b2e197616 b2e203585
        | exact resolve b2e203585 b2e197616
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197616 b2e203585
      have b2e203816 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op y y) X0) := by
        intro X0
        first
        | (have i₁ := b2e203731 X0
           have i₂ := b2e900 (σ y) X0
           grind)
        | exact superpose b2e900 b2e203731
        | exact resolve b2e203731 b2e900
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e203731
      have b2e203876 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b2e203816 X0
           have i₂ := b2e900 y X0
           grind)
        | exact superpose b2e900 b2e203816
        | exact resolve b2e203816 b2e900
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e900 b2e203816
      have b2e204259 : (M.op y y) = (M.op y (σ y)) := by
        first
        | (have i₁ := b2e197201
           have i₂ := b2e203876 (σ y)
           grind)
        | exact superpose b2e203876 b2e197201
        | exact resolve b2e197201 b2e203876
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197201 b2e203876
      have b2e204824 : (σ y) = (M.op y y) := by
        first
        | (have i₁ := b2e204259
           have i₂ := b2e1694
           grind)
        | exact superpose b2e1694 b2e204259
        | exact resolve b2e204259 b2e1694
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1694 b2e204259
      have b2e205048 : False := by grind
      exact b2e205048
    · have b3e14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x y) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b3e161 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e45 x y
           grind)
        | exact superpose b3e45 b3e16
        | (have j1 := b3e45 x y
           grind)
        | exact resolve b3e16 b3e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e45
      have b3e169 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have r₁ := b3e161
           have r₂ := b3e18
           grind)
        | exact resolve b3e161 b3e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e161
      have b3e173 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b3e169
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e169
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e169 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e169
      have b3e174 : y = (M.op x y) := by grind
      clear b3e173
      have b3e175 : False := by grind
      exact b3e175

/-- `Equation3634`: `x ◇ y = z ◇ ((w ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_y_x_pxy_Equation3634 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3634 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3634.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
        intro X0 X1 X2 X3
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e31 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op x X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 y X0 X1 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op X1 (M.op (σ x) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ y) X0 X1 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 X2 (M.op (M.op X3 X0) X1) X4 x
           have i₂ := b0e11 X0 X1 (M.op x X2) X3
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
        intro X0 X1 X4
        first
        | (have i₁ := b0e34 X0 X1 x x X4
           have i₂ := b0e11 X0 X1 x x
           grind)
        | exact superpose b0e11 b0e34
        | exact resolve b0e34 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e59 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e31 X0 x
           have i₂ := b0e36 x X0 x
           grind)
        | exact superpose b0e36 b0e31
        | exact resolve b0e31 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e141 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e36 (σ x) X0 x
           have i₂ := b0e32 X0 x
           grind)
        | exact superpose b0e32 b0e36
        | exact resolve b0e36 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e36
      have b0e596 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e141 (σ y)
           grind)
        | exact superpose b0e141 b0e18
        | exact resolve b0e18 b0e141
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141
      have b0e621 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e596
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e596
        | exact resolve b0e596 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e596
      have b0e630 : (σ x) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e621
           have i₂ := b0e59 y
           grind)
        | exact superpose b0e59 b0e621
        | exact resolve b0e621 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59 b0e621
      have b0e635 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e630
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e630
        | exact resolve b0e630 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e630
      have b0e636 : False := by grind
      exact b0e636
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op y y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : y = (k x y) := by grind
        have b1e44 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e47 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e44
        have b1e48 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e47
             have r₂ := b1e21
             grind)
          | exact resolve b1e47 b1e21
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
             have i₂ := b1e24
             grind)
          | exact superpose b1e24 b1e49
          | exact resolve b1e49 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e49
        have b1e51 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e50
             grind)
          | exact superpose b1e50 b1e19
          | exact resolve b1e19 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e50
             grind)
          | exact superpose b1e50 b1e22
          | exact resolve b1e22 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : x = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e50
             grind)
          | exact superpose b1e50 b1e13
          | exact resolve b1e13 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e56 : x = y := by
          first
          | (have i₁ := b1e55
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e55
          | exact resolve b1e55 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e59 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e51
             have i₂ := b1e52
             grind)
          | exact superpose b1e52 b1e51
          | exact resolve b1e51 b1e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e52
        have b1e60 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e59
          | exact resolve b1e59 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e59
        have b1e61 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e60
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e60
          | exact resolve b1e60 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e62 : False := by grind
        exact b1e62
      · have b2e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
          intro X0 X1 X2 X3
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : y = (k x y) := by grind
        have b2e27 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op x X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 y X0 X1 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e12 X2 (M.op (M.op X3 X0) X1) X4 x
             have i₂ := b2e12 X0 X1 (M.op x X2) X3
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (k (M.op X0 X1) (M.op (M.op X2 X0) X1)) := by
          intro X0 X1 X2
          grind
        have b2e31 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
          intro X0 X1 X4
          first
          | (have i₁ := b2e29 X0 X1 x x X4
             have i₂ := b2e12 X0 X1 x x
             grind)
          | exact superpose b2e12 b2e29
          | exact resolve b2e29 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e52 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e27 X0 x
             have i₂ := b2e31 x X0 x
             grind)
          | exact superpose b2e31 b2e27
          | exact resolve b2e27 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e76 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (σ y)
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 (M.op (σ y) (σ y)) x
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e494 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e76 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76
        have b2e495 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e494
             have r₂ := b2e22
             grind)
          | exact resolve b2e494 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e494
        have b2e496 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e495
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e495
          | exact resolve b2e495 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e495
        have b2e497 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e496
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e496
          | exact resolve b2e496 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e496
        have b2e500 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e497
             grind)
          | exact superpose b2e497 b2e19
          | exact resolve b2e19 b2e497
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e503 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = (k (σ y) (M.op (M.op X0 (σ x)) (σ y))) := by
          intro X0
          first
          | (have i₁ := b2e30 (σ x) (σ y) X0
             have i₂ := b2e497
             grind)
          | exact superpose b2e497 b2e30
          | exact resolve b2e30 b2e497
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e505 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e31 (σ x) (σ y) x
             have i₂ := b2e497
             grind)
          | exact superpose b2e497 b2e31
          | exact resolve b2e31 b2e497
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31 b2e497
        have b2e509 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b2e503 x
             have i₂ := b2e505 (M.op x (σ x))
             grind)
          | exact superpose b2e505 b2e503
          | exact resolve b2e503 b2e505
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e503 b2e505
        have b2e511 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e500
             have i₂ := b2e52 y
             grind)
          | exact superpose b2e52 b2e500
          | exact resolve b2e500 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e500
        have b2e512 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b2e509
             have i₂ := b2e18 y y
             grind)
          | exact superpose b2e18 b2e509
          | exact resolve b2e509 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e509
        have b2e513 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e511
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e511
          | exact resolve b2e511 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e511
        have b2e968 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e512
             have i₂ := b2e17 y y
             grind)
          | exact superpose b2e17 b2e512
          | (have j1 := b2e17 y y
             grind)
          | exact resolve b2e512 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e512
        have b2e979 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b2e968
        have b2e990 : (σ x) = (σ y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e979
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e979
          | exact resolve b2e979 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e979
        have b2e995 : y = (M.op y y) := by
          first
          | (have r₁ := b2e990
             have r₂ := b2e513
             grind)
          | exact resolve b2e990 b2e513
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e990
        have b2e1094 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e995
             grind)
          | exact superpose b2e995 b2e20
          | exact resolve b2e20 b2e995
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e995
        have b2e1177 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e513
             have i₂ := b2e1094
             grind)
          | exact superpose b2e1094 b2e513
          | exact resolve b2e513 b2e1094
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e513 b2e1094
        have b2e1178 : False := by grind
        exact b2e1178
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ y) = (k (σ x) (σ y)) := by grind
        have b3e25 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e24
          | exact resolve b3e24 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e26 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e25
             grind)
          | exact superpose b3e25 b3e13
          | exact resolve b3e13 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e27 : y = (k x y) := by
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
        have b3e55 : y ≠ y ∨ x = (M.op y y) ∨ x = (k x y) := by
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
        have b3e59 : x = (M.op y y) ∨ x = (k x y) := by grind
        clear b3e55
        have b3e60 : x = (k x y) := by
          first
          | (have r₁ := b3e59
             have r₂ := b3e20
             grind)
          | exact resolve b3e59 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
        have b3e61 : x = y := by
          first
          | (have i₁ := b3e60
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e60
          | exact resolve b3e60 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e60
        have b3e62 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e61
             grind)
          | exact superpose b3e61 b3e19
          | exact resolve b3e19 b3e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e65 : y = (M.op y y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e61
             grind)
          | exact superpose b3e61 b3e21
          | exact resolve b3e21 b3e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e66 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e62
             have i₂ := b3e65
             grind)
          | exact superpose b3e65 b3e62
          | exact resolve b3e62 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62 b3e65
        have b3e67 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e66
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e66
          | exact resolve b3e66 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66
        have b3e68 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e67
             have i₂ := b3e61
             grind)
          | exact superpose b3e61 b3e67
          | exact resolve b3e67 b3e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61 b3e67
        have b3e69 : False := by grind
        exact b3e69
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e31 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e13 X2 (M.op (M.op X3 X0) X1) X4 x
               have i₂ := b4e13 X0 X1 (M.op x X2) X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b4e31 X0 X1 x x X4
               have i₂ := b4e13 X0 X1 x x
               grind)
            | exact superpose b4e13 b4e31
            | exact resolve b4e31 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e94 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e33 (σ y) (σ x) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e33
            | exact resolve b4e33 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e96 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e33 y x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e33
            | exact resolve b4e33 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e195 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e94 (σ x)
               grind)
            | exact superpose b4e94 b4e20
            | exact resolve b4e20 b4e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94
          have b4e200 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e195
               have i₂ := b4e96 x
               grind)
            | exact superpose b4e96 b4e195
            | exact resolve b4e195 b4e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96 b4e195
          have b4e201 : False := by grind
          exact b4e201
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e28 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 x X0 X1 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 X2 (M.op (M.op X3 X0) X1) X4 x
               have i₂ := b5e13 X0 X1 (M.op x X2) X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b5e30 X0 X1 x x X4
               have i₂ := b5e13 X0 X1 x x
               grind)
            | exact superpose b5e13 b5e30
            | exact resolve b5e30 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e34 : ∀ X0 : G, (M.op x x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e28 x X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e28
            | exact resolve b5e28 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e44 : y ≠ y ∨ x = (M.op y y) ∨ x = (k x y) := by
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
          have b5e47 : x = (M.op y y) ∨ x = (k x y) := by grind
          clear b5e44
          have b5e48 : x = (k x y) := by
            first
            | (have r₁ := b5e47
               have r₂ := b5e21
               grind)
            | exact resolve b5e47 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e62 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 (M.op (σ y) (σ y)) x
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
          have b5e75 : ∀ X0 : G, x = (k (M.op X0 y) x) := by
            intro X0
            grind
          clear b5e34
          have b5e84 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e32 y x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e32
            | exact resolve b5e32 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e310 : x = (k y x) := by
            first
            | (have i₁ := b5e75 x
               have i₂ := b5e84 x
               grind)
            | exact superpose b5e84 b5e75
            | exact resolve b5e75 b5e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75
          have b5e481 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e62 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e482 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e481
               have r₂ := b5e24
               grind)
            | exact resolve b5e481 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e481
          have b5e483 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e482
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e482
            | exact resolve b5e482 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e482
          have b5e484 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e483
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e483
            | exact resolve b5e483 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e483
          have b5e487 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e484
               grind)
            | exact superpose b5e484 b5e20
            | exact resolve b5e20 b5e484
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e489 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b5e17 (σ y) (σ x)
               have i₂ := b5e484
               grind)
            | exact superpose b5e484 b5e17
            | (have j0 := b5e17 (σ y) (σ x)
               grind)
            | (have r₁ := b5e17 (σ y) (σ x)
               have r₂ := b5e484
               grind)
            | exact resolve b5e17 b5e484
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e492 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e32 (σ x) (σ y) x
               have i₂ := b5e484
               grind)
            | exact superpose b5e484 b5e32
            | exact resolve b5e32 b5e484
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e484
          have b5e496 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
          clear b5e489
          have b5e498 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b5e496
               have i₂ := b5e492 (σ x)
               grind)
            | exact superpose b5e492 b5e496
            | exact resolve b5e496 b5e492
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e492 b5e496
          have b5e500 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e487
               have i₂ := b5e84 x
               grind)
            | exact superpose b5e84 b5e487
            | exact resolve b5e487 b5e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84 b5e487
          have b5e502 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e498
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e498
            | exact resolve b5e498 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e498
          have b5e504 : (σ y) = (σ (k y x)) := by
            first
            | (have r₁ := b5e502
               have r₂ := b5e500
               grind)
            | exact resolve b5e502 b5e500
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e502
          have b5e505 : (σ x) = (σ y) := by
            first
            | (have i₁ := b5e504
               have i₂ := b5e310
               grind)
            | exact superpose b5e310 b5e504
            | exact resolve b5e504 b5e310
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e310 b5e504
          have b5e506 : False := by grind
          exact b5e506
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
          intro X0 X1 X2 X3
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op y y) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
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
        have b6e40 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e12 X2 (M.op (M.op X3 X0) X1) X4 x
             have i₂ := b6e12 X0 X1 (M.op x X2) X3
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e42 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
          intro X0 X1 X4
          first
          | (have i₁ := b6e40 X0 X1 x x X4
             have i₂ := b6e12 X0 X1 x x
             grind)
          | exact superpose b6e12 b6e40
          | exact resolve b6e40 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b6e74 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
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
        have b6e91 : y = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e74
             have r₂ := b6e20
             grind)
          | exact resolve b6e74 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e100 : y = (M.op x y) := by
          first
          | (have r₁ := b6e91
             have r₂ := b6e21
             grind)
          | exact resolve b6e91 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e91
        have b6e110 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b6e42 x y x
             have i₂ := b6e100
             grind)
          | exact superpose b6e100 b6e42
          | exact resolve b6e42 b6e100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e100
        have b6e123 : y = (k y y) := by grind
        have b6e128 : x ≠ y := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e110 y
             grind)
          | exact superpose b6e110 b6e20
          | exact resolve b6e20 b6e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e110
        have b6e658 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e72 y y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e72
          | exact resolve b6e72 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e730 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by grind
        clear b6e658
        have b6e756 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e730
             have i₂ := b6e123
             grind)
          | exact superpose b6e123 b6e730
          | exact resolve b6e730 b6e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e123 b6e730
        have b6e757 : (σ x) = (σ y) := by grind
        clear b6e756
        have b6e869 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e757
             grind)
          | exact superpose b6e757 b6e13
          | exact resolve b6e13 b6e757
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e757
        have b6e882 : x = y := by
          first
          | (have i₁ := b6e869
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e869
          | exact resolve b6e869 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e869
        have b6e887 : False := by grind
        exact b6e887
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op y y) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e13 X2 (M.op (M.op X3 X0) X1) X4 x
               have i₂ := b7e13 X0 X1 (M.op x X2) X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e31 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (k (M.op X0 X1) (M.op (M.op X2 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b7e32 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b7e30 X0 X1 x x X4
               have i₂ := b7e13 X0 X1 x x
               grind)
            | exact superpose b7e13 b7e30
            | exact resolve b7e30 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e38 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X2 x X0
               have i₂ := b7e32 (M.op X0 X1) X2 x
               grind)
            | exact superpose b7e32 b7e13
            | exact resolve b7e13 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e43 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e46 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e43
          have b7e48 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e46
               have r₂ := b7e23
               grind)
            | exact resolve b7e46 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e50 : (σ x) = (σ (k x y)) := by
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
          have b7e53 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e14
            | exact resolve b7e14 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e54 : x = (k x y) := by
            first
            | (have i₁ := b7e53
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e53
            | exact resolve b7e53 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e91 : x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e54
               grind)
            | exact superpose b7e54 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e92 : x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e91
               have r₂ := b7e21
               grind)
            | exact resolve b7e91 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e94 : x = (M.op x y) := by
            first
            | (have r₁ := b7e92
               have r₂ := b7e22
               grind)
            | exact resolve b7e92 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e102 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e32 x y x
               have i₂ := b7e94
               grind)
            | exact superpose b7e94 b7e32
            | exact resolve b7e32 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e123 : x ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e102 y
               grind)
            | exact superpose b7e102 b7e22
            | exact resolve b7e22 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102
          have b7e216 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ x)) = (k (σ y) (M.op (M.op X0 (σ y)) (σ x))) := by
            intro X0
            first
            | (have i₁ := b7e31 (σ y) (σ x) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e31
            | exact resolve b7e31 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e241 : (M.op (σ y) (σ x)) = (k (σ y) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b7e216 x
               have i₂ := b7e38 x (σ y) (σ x)
               grind)
            | exact superpose b7e38 b7e216
            | exact resolve b7e216 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38 b7e216
          have b7e253 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e241
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e241
            | exact resolve b7e241 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e241
          have b7e255 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e253
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e253
            | exact resolve b7e253 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e253
          have b7e416 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e255
               grind)
            | exact superpose b7e255 b7e14
            | exact resolve b7e14 b7e255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e255
          have b7e418 : y = (k y y) := by
            first
            | (have i₁ := b7e416
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e416
            | exact resolve b7e416 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e416
          have b7e589 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e418
               grind)
            | exact superpose b7e418 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e418
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e418
          have b7e590 : y = (M.op y y) := by grind
          clear b7e589
          have b7e816 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e32 y y x
               have i₂ := b7e590
               grind)
            | exact superpose b7e590 b7e32
            | exact resolve b7e32 b7e590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e590
          have b7e890 : x = y := by
            first
            | (have i₁ := b7e94
               have i₂ := b7e816 x
               grind)
            | exact superpose b7e816 b7e94
            | exact resolve b7e94 b7e816
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94 b7e816
          have b7e892 : False := by grind
          exact b7e892
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y y) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e74 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e248 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e74 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e249 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e248
               have r₂ := b8e24
               grind)
            | exact resolve b8e248 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e248
          have b8e250 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e249
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e249
            | exact resolve b8e249 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e249
          have b8e251 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e250
               grind)
            | exact superpose b8e250 b8e20
            | exact resolve b8e20 b8e250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e250
          have b8e377 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e251
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e251
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e251 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e251
          have b8e378 : x = (M.op y y) ∨ y = (M.op y x) := by grind
          clear b8e377
          have b8e380 : y = (M.op y x) := by
            first
            | (have r₁ := b8e378
               have r₂ := b8e21
               grind)
            | exact resolve b8e378 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e378
          have b8e382 : False := by grind
          exact b8e382

/-- `Equation3714`: `x ◇ y = (x ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_y_pyx_Equation3714 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3714 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3714.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = b :=
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
      have b0e75 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e29
      have b0e80 : False := by grind
      exact b0e80
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
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
            intro X0 X1
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e30
          have b4e36 : x = (M.op x x) := by
            first
            | (have i₁ := b4e13 y y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b4e59 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e52 X0 X1
               have i₂ := b4e31 X0
               grind)
            | exact superpose b4e31 b4e52
            | (have j0 := b4e52 X0 X1
               grind)
            | exact resolve b4e52 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e52
          have b4e215 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b4e59 X0 x
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e59
            | (have j0 := b4e59 X0 x
               grind)
            | (have r₁ := b4e59 X0 x
               have r₂ := b4e36
               grind)
            | exact resolve b4e59 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59
          have b4e217 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ x = X0 := by
            intro X0
            first
            | (have j0 := b4e215 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e215
          have b4e453 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e63 x y
               grind)
            | exact superpose b4e63 b4e20
            | (have j1 := b4e63 x y
               grind)
            | exact resolve b4e20 b4e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e63
          have b4e503 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have r₁ := b4e453
               have r₂ := b4e23
               grind)
            | exact resolve b4e453 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e453
          have b4e523 : (σ x) = (σ y) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b4e503
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e503
            | exact resolve b4e503 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e503
          have b4e533 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b4e523
               have r₂ := b4e23
               grind)
            | exact resolve b4e523 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e523
          have b4e538 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b4e533
               have i₂ := b4e217 y
               grind)
            | exact superpose b4e217 b4e533
            | (have j1 := b4e217 y
               grind)
            | exact resolve b4e533 b4e217
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e217 b4e533
          have b4e546 : x = y := by grind
          clear b4e538
          have b4e550 : False := by grind
          exact b4e550
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
          have b5e91 : (σ x) ≠ (σ (M.op y y)) := by
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
          have b5e98 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e91
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e91
            | exact resolve b5e91 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e91
          have b5e99 : False := by grind
          exact b5e99
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
          have b7e111 : (σ x) = (σ (M.op y y)) := by
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
          have b7e139 : (M.op y y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e111
               grind)
            | exact superpose b7e111 b7e14
            | exact resolve b7e14 b7e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111
          have b7e140 : x = (M.op y y) := by
            first
            | (have i₁ := b7e139
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e139
            | exact resolve b7e139 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e139
          have b7e144 : False := by grind
          exact b7e144
        · have b8e13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
            intro X0 X1
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
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e30
          have b8e60 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e65 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op (M.op X1 X1) X0) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 X1
               have i₂ := b8e18 X0 (M.op X1 X1)
               grind)
            | (have i₁ := b8e13 X0 X1
               have i₂ := b8e18 (M.op (M.op X0 X0) (M.op X1 X0)) X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X0 (M.op X1 X1)
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e66 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (M.op (σ y) (σ y))
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (M.op (σ y) (σ y)) (σ x)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e68 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e65 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e60 X0 X1
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e60
            | (have j0 := b8e60 X0 X1
               grind)
            | exact resolve b8e60 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e80 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 (σ X0) X1
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e13
            | exact resolve b8e13 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e218 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have j0 := b8e66 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e219 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e218
               have r₂ := b8e23
               grind)
            | exact resolve b8e218 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e218
          have b8e220 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e219
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e219
            | exact resolve b8e219 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e219
          have b8e339 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e71 x y
               grind)
            | exact superpose b8e71 b8e20
            | (have j1 := b8e71 x y
               grind)
            | exact resolve b8e20 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e388 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e339
               have r₂ := b8e23
               grind)
            | exact resolve b8e339 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e339
          have b8e1059 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e388
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e388
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e388
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e388
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e388 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e388
          have b8e1061 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = y := by grind
          clear b8e1059
          have b8e1066 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b8e1061
               have r₂ := b8e21
               grind)
            | exact resolve b8e1061 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1061
          have b8e1073 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e14 (M.op x x)
               have i₂ := b8e1066
               grind)
            | exact superpose b8e1066 b8e14
            | exact resolve b8e14 b8e1066
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1066
          have b8e1106 : y = (M.op x x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e1073
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e1073
            | exact resolve b8e1073 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1073
          have b8e1107 : y = (M.op x x) := by grind
          clear b8e1106
          have b8e1140 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b8e13 x X0
               have i₂ := b8e1107
               grind)
            | exact superpose b8e1107 b8e13
            | exact resolve b8e13 b8e1107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1145 : ∀ X0 : G, (M.op y X0) = (k X0 y) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b8e68 X0 x
               have i₂ := b8e1107
               grind)
            | exact superpose b8e1107 b8e68
            | exact resolve b8e68 b8e1107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e1146 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b8e80 x X0
               have i₂ := b8e1107
               grind)
            | exact superpose b8e1107 b8e80
            | exact resolve b8e80 b8e1107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80
          have b8e1157 : y = (M.op y y) := by
            first
            | (have i₁ := b8e13 x x
               have i₂ := b8e1107
               grind)
            | exact superpose b8e1107 b8e13
            | exact resolve b8e13 b8e1107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1107
          have b8e1868 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op y (τ X0))) ∨ (τ X0) = y := by
            intro X0
            first
            | (have i₁ := b8e27 X0 y
               have i₂ := b8e1145 (τ X0)
               grind)
            | exact superpose b8e1145 b8e27
            | (have j1 := b8e1145 (τ X0)
               grind)
            | exact resolve b8e27 b8e1145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27
          have b8e2330 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (k x y))) := by
            first
            | (have i₁ := b8e1146 (σ y)
               have i₂ := b8e220
               grind)
            | exact superpose b8e220 b8e1146
            | exact resolve b8e1146 b8e220
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e220 b8e1146
          have b8e2949 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y x))) ∨ x = y := by
            first
            | (have i₁ := b8e2330
               have i₂ := b8e1145 x
               grind)
            | exact superpose b8e1145 b8e2330
            | (have j1 := b8e1145 x
               grind)
            | exact resolve b8e2330 b8e1145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1145 b8e2330
          have b8e2984 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y x))) := by
            first
            | (have r₁ := b8e2949
               have r₂ := b8e21
               grind)
            | exact resolve b8e2949 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2949
          have b8e3047 : (M.op (σ x) (σ y)) = (σ (k (M.op y x) y)) ∨ (σ (M.op y y)) = (σ (M.op y x)) ∨ (σ y) = (σ (M.op y x)) := by
            first
            | (have i₁ := b8e71 y (M.op y x)
               have i₂ := b8e2984
               grind)
            | exact superpose b8e2984 b8e71
            | (have j0 := b8e71 y (M.op y x)
               grind)
            | exact resolve b8e71 b8e2984
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71
          have b8e3059 : (σ y) = (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (k (M.op y x) y)) ∨ (σ y) = (σ (M.op y x)) := by
            first
            | (have i₁ := b8e3047
               have i₂ := b8e1157
               grind)
            | exact superpose b8e1157 b8e3047
            | exact resolve b8e3047 b8e1157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3047
          have b8e3060 : (M.op (σ x) (σ y)) = (σ (k (M.op y x) y)) ∨ (σ y) = (σ (M.op y x)) := by grind
          clear b8e3059
          have b8e3600 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op y X0)) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b8e1868 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e1868
            | exact resolve b8e1868 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1868
          have b8e3641 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op y X0)) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b8e3600 X0
               have i₂ := b8e19 X0 y
               grind)
            | exact superpose b8e19 b8e3600
            | (have j0 := b8e3600 X0
               grind)
            | exact resolve b8e3600 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3600
          have b8e60642 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op y x))) ∨ y = (M.op y x) ∨ (σ y) = (σ (M.op y x)) := by
            first
            | (have i₁ := b8e3641 (M.op y x)
               have i₂ := b8e3060
               grind)
            | exact superpose b8e3060 b8e3641
            | (have j0 := b8e3641 (M.op y x)
               grind)
            | exact resolve b8e3641 b8e3060
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3060 b8e3641
          have b8e60648 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (σ (M.op y x)) := by
            first
            | (have i₁ := b8e60642
               have i₂ := b8e1140 y
               grind)
            | exact superpose b8e1140 b8e60642
            | exact resolve b8e60642 b8e1140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60642
          have b8e60651 : (σ y) = (σ (M.op y x)) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b8e60648
               have r₂ := b8e20
               grind)
            | exact resolve b8e60648 b8e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60648
          have b8e60657 : (τ (σ y)) = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e14 (M.op y x)
               have i₂ := b8e60651
               grind)
            | exact superpose b8e60651 b8e14
            | exact resolve b8e14 b8e60651
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60651
          have b8e60749 : y = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e60657
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e60657
            | exact resolve b8e60657 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60657
          have b8e60750 : y = (M.op y x) := by grind
          clear b8e60749
          have b8e60757 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b8e2984
               have i₂ := b8e60750
               grind)
            | exact superpose b8e60750 b8e2984
            | exact resolve b8e2984 b8e60750
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2984
          have b8e60763 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1140 y
               have i₂ := b8e60750
               grind)
            | exact superpose b8e60750 b8e1140
            | exact resolve b8e1140 b8e60750
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1140 b8e60750
          have b8e60821 : y = (M.op x y) := by
            first
            | (have i₁ := b8e60763
               have i₂ := b8e1157
               grind)
            | exact superpose b8e1157 b8e60763
            | exact resolve b8e60763 b8e1157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60763
          have b8e60826 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e60757
               have i₂ := b8e31 y
               grind)
            | exact superpose b8e31 b8e60757
            | exact resolve b8e60757 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31 b8e60757
          have b8e60846 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e60826
               have i₂ := b8e1157
               grind)
            | exact superpose b8e1157 b8e60826
            | exact resolve b8e60826 b8e1157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1157 b8e60826
          have b8e62103 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e60846
               grind)
            | exact superpose b8e60846 b8e20
            | exact resolve b8e20 b8e60846
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60846
          have b8e62214 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b8e62103
               have i₂ := b8e60821
               grind)
            | exact superpose b8e60821 b8e62103
            | exact resolve b8e62103 b8e60821
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60821 b8e62103
          have b8e62215 : False := by grind
          exact b8e62215

/-- `Equation3718`: `x ◇ y = (x ◇ x) ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pyx_Equation3718 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3718 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3718.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : (M.op x y) = (M.op x x) := by grind
      have b0e18 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e16
        | exact resolve b0e16 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e20 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
      have b0e54 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e13 (σ x) (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e13
        | (have j0 := b0e13 (σ x) (σ x)
           grind)
        | (have r₁ := b0e13 (σ x) (σ y)
           have r₂ := b0e18
           grind)
        | exact resolve b0e13 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
        first
        | (have i₁ := b0e13 x y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e13
        | (have j0 := b0e13 x x
           grind)
        | (have r₁ := b0e13 x y
           have r₂ := b0e17
           grind)
        | exact resolve b0e13 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e60 : (M.op x x) = (k x y) := by grind
      clear b0e55
      have b0e61 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e54
      have b0e63 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e61
           have i₂ := b0e15 x y
           grind)
        | exact superpose b0e15 b0e61
        | exact resolve b0e61 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61
      have b0e65 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e63
           have i₂ := b0e60
           grind)
        | exact superpose b0e60 b0e63
        | exact resolve b0e63 b0e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60 b0e63
      have b0e67 : False := by grind
      exact b0e67
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X2 X1)) := by
        intro X0 X1 X2
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b1e17 : (M.op x y) = (M.op x x) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e19 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e16
        | exact resolve b1e16 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
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
      have b1e21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e15
        | exact resolve b1e15 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e22 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 X1)) = (M.op (M.op X0 X0) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (M.op X0 X0) X1 X2
           have i₂ := b1e10 X0 X0 X0
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e23 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 X0) (M.op x x)) := by
        intro X0
        first
        | (have i₁ := b1e10 X0 y x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X2 (M.op X3 X1) (M.op X0 X0)
           have i₂ := b1e10 X0 X1 X3
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e25 : ∀ X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op X3 X1)) := by
        intro X1 X2 X3
        first
        | (have i₁ := b1e24 x X1 X2 X3
           have i₂ := b1e10 X2 X1 x
           grind)
        | exact superpose b1e10 b1e24
        | exact resolve b1e24 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e24
      have b1e26 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b1e23 X0
           have i₂ := b1e10 X0 x x
           grind)
        | exact superpose b1e10 b1e23
        | exact resolve b1e23 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23
      have b1e27 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e22 X0 X1 x
           have i₂ := b1e10 X0 X1 x
           grind)
        | exact superpose b1e10 b1e22
        | exact resolve b1e22 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22
      have b1e46 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
        first
        | (have i₁ := b1e13 x y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e13
        | (have j0 := b1e13 x x
           grind)
        | (have r₁ := b1e13 x y
           have r₂ := b1e17
           grind)
        | exact resolve b1e13 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e48 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 x) ∨ (M.op X0 X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b1e13 X0 y
           have i₂ := b1e26 X0
           grind)
        | exact superpose b1e26 b1e13
        | (have j0 := b1e13 X0 x
           grind)
        | (have r₁ := b1e13 x y
           have r₂ := b1e26 x
           grind)
        | (have r₁ := b1e13 y x
           have r₂ := b1e26 y
           grind)
        | exact resolve b1e13 b1e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e49 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e13 X0 (M.op X2 X1)
           have i₂ := b1e25 X1 X0 X2
           grind)
        | exact superpose b1e25 b1e13
        | (have j0 := b1e13 X0 X1
           grind)
        | (have r₁ := b1e13 (M.op x X1) X1
           have r₂ := b1e25 X1 (M.op x X1) x
           grind)
        | (have r₁ := b1e13 X1 (M.op x X1)
           have r₂ := b1e25 X1 X1 x
           grind)
        | exact resolve b1e13 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 (M.op X1 X1) X1
           have i₂ := b1e10 X1 X1 X1
           grind)
        | exact superpose b1e10 b1e13
        | exact resolve b1e13 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e51 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op y x) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b1e13 y x
           have i₂ := b1e26 y
           grind)
        | exact superpose b1e26 b1e13
        | (have r₁ := b1e13 x y
           have r₂ := b1e26 x
           grind)
        | (have r₁ := b1e13 y x
           have r₂ := b1e26 y
           grind)
        | exact resolve b1e13 b1e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e52 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e13 (M.op x X1) X1
           have i₂ := b1e25 X1 (M.op x X1) x
           grind)
        | exact superpose b1e25 b1e13
        | (have r₁ := b1e13 (M.op x X1) X1
           have r₂ := b1e25 X1 (M.op x X1) x
           grind)
        | (have r₁ := b1e13 X1 (M.op x X1)
           have r₂ := b1e25 X1 X1 x
           grind)
        | exact resolve b1e13 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b1e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e54 : (M.op x x) = (k x y) := by grind
      clear b1e46
      have b1e55 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e50 X0 X1
           have i₂ := b1e27 X0 X1
           grind)
        | exact superpose b1e27 b1e50
        | (have j0 := b1e50 X0 X1
           grind)
        | (have r₁ := b1e50 X1 X1
           have r₂ := b1e27 X1 X1
           grind)
        | exact resolve b1e50 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e50
      have b1e59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e15 X0 X0
           have i₂ := b1e53 (σ X0)
           grind)
        | exact superpose b1e53 b1e15
        | exact resolve b1e15 b1e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
      clear b1e59
      have b1e69 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 X0 X1
           have i₂ := b1e14 X0 X1
           grind)
        | (have i₁ := b1e13 X0 X0
           have i₂ := b1e14 X0 X1
           grind)
        | exact superpose b1e14 b1e13
        | (have j0 := b1e13 X0 X0
           have j1 := b1e14 X0 X1
           grind)
        | (have r₁ := b1e13 X0 X1
           have r₂ := b1e14 X0 X1
           grind)
        | (have r₁ := b1e13 X1 X1
           have r₂ := b1e14 X1 X1
           grind)
        | exact resolve b1e13 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e75 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e13 X1 X1
           have i₂ := b1e14 X1 X1
           grind)
        | (have i₁ := b1e13 X0 X1
           have i₂ := b1e14 X0 X1
           grind)
        | exact superpose b1e14 b1e13
        | (have j1 := b1e14 X0 X1
           grind)
        | (have r₁ := b1e13 X0 X1
           have r₂ := b1e14 X0 X1
           grind)
        | (have r₁ := b1e13 X1 X1
           have r₂ := b1e14 X1 X1
           grind)
        | exact resolve b1e13 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e79 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 X1)) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 X2 X0 X0
           have i₂ := b1e14 X0 X1
           grind)
        | (have i₁ := b1e10 X0 X1 X0
           have i₂ := b1e14 X0 X1
           grind)
        | exact superpose b1e14 b1e10
        | (have j1 := b1e14 X0 X1
           grind)
        | exact resolve b1e10 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X1 X0
           have i₂ := b1e14 (σ X1) (σ X0)
           grind)
        | exact superpose b1e14 b1e15
        | (have j1 := b1e14 (σ X1) (σ X0)
           grind)
        | exact resolve b1e15 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e84 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b1e69 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e69
      have b1e85 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e82 X0 X1
           have i₂ := b1e60 X1
           grind)
        | exact superpose b1e60 b1e82
        | (have j0 := b1e82 X0 X1
           grind)
        | exact resolve b1e82 b1e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e82
      have b1e88 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e79 X0 X1 X2
           have i₂ := b1e10 X2 X1 X0
           grind)
        | exact superpose b1e10 b1e79
        | (have j0 := b1e79 X0 X1 X2
           grind)
        | exact resolve b1e79 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e79
      have b1e179 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b1e20 X0 (τ X0)
           have i₂ := b1e53 (τ X0)
           grind)
        | exact superpose b1e53 b1e20
        | exact resolve b1e20 b1e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e183 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k (τ X0) X1)
           have i₂ := b1e20 X0 X1
           grind)
        | exact superpose b1e20 b1e11
        | exact resolve b1e11 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20
      have b1e184 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b1e179 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e179
        | exact resolve b1e179 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e179
      have b1e185 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b1e184 X0
           have i₂ := b1e53 X0
           grind)
        | exact superpose b1e53 b1e184
        | exact resolve b1e184 b1e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53 b1e184
      have b1e225 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b1e84 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e256 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e27 (σ X0) X1
           have i₂ := b1e60 X0
           grind)
        | exact superpose b1e60 b1e27
        | exact resolve b1e27 b1e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e261 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e25 (σ X0) X1 (σ X0)
           have i₂ := b1e60 X0
           grind)
        | exact superpose b1e60 b1e25
        | exact resolve b1e25 b1e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e295 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e13 X1 X1
           have i₂ := b1e88 X0 X1 X1
           grind)
        | (have i₁ := b1e13 X0 X1
           have i₂ := b1e88 X0 X1 X0
           grind)
        | exact superpose b1e88 b1e13
        | (have j1 := b1e88 X1 X0 X2
           grind)
        | (have r₁ := b1e13 X0 X1
           have r₂ := b1e88 X0 X1 X0
           grind)
        | (have r₁ := b1e13 X1 X0
           have r₂ := b1e88 X0 X1 X1
           grind)
        | exact resolve b1e13 b1e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e307 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b1e19
           have i₂ := b1e88 X0 (σ y) (σ x)
           grind)
        | (have i₁ := b1e19
           have i₂ := b1e88 (σ y) x (σ x)
           grind)
        | exact superpose b1e88 b1e19
        | (have j1 := b1e88 X0 (σ y) x
           grind)
        | exact resolve b1e19 b1e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e318 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (k (M.op X3 X2) X1) = (M.op X1 (M.op X3 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e25 X2 X0 X3
           have i₂ := b1e88 (M.op X3 X2) X1 X0
           grind)
        | (have i₁ := b1e25 X1 X2 X3
           have i₂ := b1e88 X0 (M.op X3 X1) X2
           grind)
        | exact superpose b1e88 b1e25
        | (have j1 := b1e88 X2 X1 X0
           grind)
        | exact resolve b1e25 b1e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e319 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 x) ∨ (M.op X1 y) = (k y X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e26 X0
           have i₂ := b1e88 y X1 X0
           grind)
        | (have i₁ := b1e26 x
           have i₂ := b1e88 X0 y x
           grind)
        | exact superpose b1e88 b1e26
        | (have j1 := b1e88 x X1 X0
           grind)
        | exact resolve b1e26 b1e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e324 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e19
           have i₂ := b1e88 (σ y) X0 (σ x)
           grind)
        | (have i₁ := b1e19
           have i₂ := b1e88 X0 (σ y) (σ x)
           grind)
        | exact superpose b1e88 b1e19
        | (have j1 := b1e88 (σ y) X0 x
           grind)
        | exact resolve b1e19 b1e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e327 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X2 (σ X1)) = (M.op X2 (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e15 X1 X0
           have i₂ := b1e88 (σ X1) (σ X0) X2
           grind)
        | exact superpose b1e88 b1e15
        | (have j1 := b1e88 (σ X0) (σ X1) X2
           grind)
        | exact resolve b1e15 b1e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e88
      have b1e334 : ∀ X0 X1 : G, (M.op X1 x) = (k y X1) ∨ (M.op X0 X1) = (M.op X0 x) := by
        intro X0 X1
        first
        | (have i₁ := b1e319 X0 X1
           have i₂ := b1e26 X1
           grind)
        | exact superpose b1e26 b1e319
        | (have j0 := b1e319 X0 X1
           grind)
        | exact resolve b1e319 b1e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e319
      have b1e335 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (k (M.op X3 X2) X1) ∨ (M.op X0 X1) = (M.op X0 X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e318 X0 X1 X2 X3
           have i₂ := b1e25 X2 X1 X3
           grind)
        | exact superpose b1e25 b1e318
        | (have j0 := b1e318 X0 X1 X2 X3
           grind)
        | exact resolve b1e318 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e318
      have b1e356 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e183 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e183
        | exact resolve b1e183 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e394 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
        intro X0
        first
        | (have j0 := b1e55 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e55
      have b1e617 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b1e11 (M.op (τ X0) (τ X0))
           have i₂ := b1e185 X0
           grind)
        | exact superpose b1e185 b1e11
        | exact resolve b1e11 b1e185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e682 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (σ X0) (σ X1)) (M.op (σ X0) (σ X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e60 (M.op X1 X1)
           have i₂ := b1e85 X0 X1
           grind)
        | exact superpose b1e85 b1e60
        | (have j1 := b1e85 X1 X0
           grind)
        | exact resolve b1e60 b1e85
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e697 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e25 (σ X0) X2 (σ X1)
           have i₂ := b1e85 X1 X0
           grind)
        | exact superpose b1e85 b1e25
        | (have j1 := b1e85 X1 X0
           grind)
        | exact resolve b1e25 b1e85
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e85
      have b1e708 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (σ X0) (σ X1)) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e682 X0 X1
           have i₂ := b1e25 (σ X1) (M.op (σ X0) (σ X1)) (σ X0)
           grind)
        | exact superpose b1e25 b1e682
        | (have j0 := b1e682 X0 X1
           grind)
        | exact resolve b1e682 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e682
      have b1e739 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ X0) (σ X1)) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e708 X0 X1
           have i₂ := b1e10 X0 X0 X0
           grind)
        | exact superpose b1e10 b1e708
        | (have j0 := b1e708 X0 X1
           grind)
        | exact resolve b1e708 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e708
      have b1e1121 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (τ (M.op X0 X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e27 (τ X0) X1
           have i₂ := b1e617 X0
           grind)
        | exact superpose b1e617 b1e27
        | exact resolve b1e27 b1e617
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1190 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b1e75 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e75
      have b1e1473 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X1)) X2) = (M.op (σ (M.op (M.op X0 X1) X1)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e256 (M.op X0 X1) X2
           have i₂ := b1e25 X1 (M.op X0 X1) X0
           grind)
        | exact superpose b1e25 b1e256
        | exact resolve b1e256 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1871 : (M.op y x) = (k y x) := by
        first
        | (have j0 := b1e51 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e51
      have b1e2328 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X1)) X2) = (M.op (τ (M.op (M.op X0 X1) X1)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e1121 (M.op X0 X1) X2
           have i₂ := b1e25 X1 (M.op X0 X1) X0
           grind)
        | exact superpose b1e25 b1e1121
        | exact resolve b1e1121 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1121
      have b1e2992 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 x) = (k X0 y) ∨ (M.op X0 x) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b1e48 x
           have i₂ := b1e334 x x
           grind)
        | (have i₁ := b1e48 x
           have i₂ := b1e334 x x
           grind)
        | exact superpose b1e334 b1e48
        | (have j1 := b1e334 X0 X0
           grind)
        | (have r₁ := b1e48 x
           have r₂ := b1e334 x x
           grind)
        | (have r₁ := b1e48 x
           have r₂ := b1e334 x x
           grind)
        | exact resolve b1e48 b1e334
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e48 b1e334
      have b1e3070 : ∀ X0 : G, (M.op X0 x) = (k X0 y) ∨ (M.op X0 x) = (k y X0) := by
        intro X0
        first
        | (have j0 := b1e2992 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2992
      have b1e3426 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b1e1190 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1190
      have b1e5177 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e49 X0 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e49
      have b1e5331 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e5177 X0 X0
           have i₂ := b1e84 X0 X1
           grind)
        | exact superpose b1e84 b1e5177
        | (have j1 := b1e84 X0 X1
           grind)
        | exact resolve b1e5177 b1e84
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5177
      have b1e6245 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k (M.op X2 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e394 X1
           have i₂ := b1e335 X1 X1 X2 x
           grind)
        | (have i₁ := b1e394 X2
           have i₂ := b1e335 X2 X1 X2 x
           grind)
        | exact superpose b1e335 b1e394
        | (have j1 := b1e335 X0 X0 X1 X0
           grind)
        | exact resolve b1e394 b1e335
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e335 b1e394
      have b1e14470 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e307 (σ x)
           have i₂ := b1e60 x
           grind)
        | exact superpose b1e60 b1e307
        | (have j0 := b1e307 (σ x)
           grind)
        | (have r₁ := b1e307 (σ x)
           have r₂ := b1e60 x
           grind)
        | exact resolve b1e307 b1e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e14483 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op (σ y) (M.op X1 X0)) = (k (M.op X1 X0) (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e307 (M.op X1 X0)
           have i₂ := b1e25 X0 (σ x) X1
           grind)
        | exact superpose b1e25 b1e307
        | (have j0 := b1e307 X0
           grind)
        | exact resolve b1e307 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e307
      have b1e14494 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
      clear b1e14470
      have b1e14502 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op (σ y) X0) = (k (M.op X1 X0) (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e14483 X0 X1
           have i₂ := b1e25 X0 (σ y) X1
           grind)
        | exact superpose b1e25 b1e14483
        | (have j0 := b1e14483 X0 X1
           grind)
        | exact resolve b1e14483 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e14483
      have b1e14509 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e14494
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e14494
        | exact resolve b1e14494 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e14494
      have b1e14515 : (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e14509
           have i₂ := b1e54
           grind)
        | exact superpose b1e54 b1e14509
        | exact resolve b1e14509 b1e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54 b1e14509
      have b1e14596 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b1e324 (σ x)
           have i₂ := b1e60 x
           grind)
        | exact superpose b1e60 b1e324
        | (have j0 := b1e324 (σ x)
           grind)
        | (have r₁ := b1e324 (σ x)
           have r₂ := b1e60 x
           grind)
        | exact resolve b1e324 b1e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e324
      have b1e14620 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
      clear b1e14596
      have b1e14633 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b1e14620
           have i₂ := b1e15 y x
           grind)
        | exact superpose b1e15 b1e14620
        | exact resolve b1e14620 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e14620
      have b1e14638 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
        first
        | (have i₁ := b1e14633
           have i₂ := b1e1871
           grind)
        | exact superpose b1e1871 b1e14633
        | exact resolve b1e14633 b1e1871
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e14633
      have b1e14647 : (σ (M.op x x)) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b1e19
           have i₂ := b1e14638
           grind)
        | exact superpose b1e14638 b1e19
        | exact resolve b1e19 b1e14638
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19 b1e14638
      have b1e20174 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e327 X0 X1 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e327
      have b1e20175 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e20174 X0 X1
           have i₂ := b1e60 X0
           grind)
        | exact superpose b1e60 b1e20174
        | (have j0 := b1e20174 X0 X1
           grind)
        | exact resolve b1e20174 b1e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20174
      have b1e20384 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X1) X0) ∨ (k X0 (M.op X2 X1)) = (M.op (M.op X2 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e3426 X0 (M.op X2 X1)
           have i₂ := b1e25 X1 X0 X2
           grind)
        | exact superpose b1e25 b1e3426
        | (have j0 := b1e3426 X0 (M.op X2 X1)
           grind)
        | exact resolve b1e3426 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e20468 : ∀ X0 : G, (M.op X0 x) ≠ (M.op y X0) ∨ (M.op X0 x) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b1e3426 y X0
           have i₂ := b1e26 X0
           grind)
        | exact superpose b1e26 b1e3426
        | exact resolve b1e3426 b1e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3426
      have b1e36047 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b1e295 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e295
      have b1e36404 : ∀ X0 : G, (M.op X0 x) = (M.op y X0) ∨ (M.op X0 x) = (k y X0) ∨ (M.op y X0) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b1e3070 X0
           have i₂ := b1e36047 y X0
           grind)
        | exact superpose b1e36047 b1e3070
        | (have j0 := b1e3070 X0
           have j1 := b1e36047 y X0
           grind)
        | exact resolve b1e3070 b1e36047
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3070
      have b1e36483 : ∀ X0 : G, (M.op X0 x) = (k y X0) ∨ (M.op y X0) = (k y X0) := by
        intro X0
        first
        | (have j0 := b1e36404 X0
           have j1 := b1e20468 X0
           grind)
        | (have r₁ := b1e36404 X0
           have r₂ := b1e20468 X0
           grind)
        | exact resolve b1e36404 b1e20468
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e36404
      have b1e41060 : ∀ X0 X1 X2 : G, (M.op X2 (σ (τ X0))) = (M.op X2 (σ (τ (k X0 X1)))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e697 (τ X0) (τ X1) X2
           have i₂ := b1e356 X1 X0
           grind)
        | exact superpose b1e356 b1e697
        | (have j0 := b1e697 (τ X0) (τ X1) X2
           grind)
        | exact resolve b1e697 b1e356
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e356 b1e697
      have b1e41772 : ∀ X0 X1 X2 : G, (M.op X2 (k X0 X1)) = (M.op X2 (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e41060 X0 X1 X2
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e41060
        | (have j0 := b1e41060 X0 X1 X2
           grind)
        | exact resolve b1e41060 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e41060
      have b1e41862 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (k X0 X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e41772 X0 X1 X2
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e41772
        | (have j0 := b1e41772 X0 X1 X2
           grind)
        | exact resolve b1e41772 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e41772
      have b1e41912 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e41862 X0 X1 X2
           have i₂ := b1e12 X1
           grind)
        | exact superpose b1e12 b1e41862
        | (have j0 := b1e41862 X0 X1 X2
           grind)
        | exact resolve b1e41862 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e41862
      have b1e41944 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e41912 X0 X1 X2
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e41912
        | (have j0 := b1e41912 X0 X1 X2
           grind)
        | exact resolve b1e41912 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e41912
      have b1e41965 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e41944 X0 X1 X2
           have i₂ := b1e185 X0
           grind)
        | exact superpose b1e185 b1e41944
        | (have j0 := b1e41944 X0 X1 X2
           grind)
        | exact resolve b1e41944 b1e185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e41944
      have b1e45223 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) := by
        intro X0 X1
        first
        | (have j0 := b1e52 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e52
      have b1e45418 : ∀ X0 : G, (M.op (M.op X0 x) y) = (k (M.op X0 x) y) := by
        intro X0
        first
        | (have i₁ := b1e45223 X0 y
           have i₂ := b1e26 X0
           grind)
        | exact superpose b1e26 b1e45223
        | exact resolve b1e45223 b1e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e45546 : ∀ X0 X1 : G, (τ (M.op (M.op X0 (σ X1)) (σ X1))) = (k (τ (M.op X0 (σ X1))) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e183 (M.op X0 (σ X1)) X1
           have i₂ := b1e45223 X0 (σ X1)
           grind)
        | exact superpose b1e45223 b1e183
        | exact resolve b1e183 b1e45223
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e45223
      have b1e45629 : ∀ X0 : G, (M.op (M.op X0 x) x) = (k (M.op X0 x) y) := by
        intro X0
        first
        | (have i₁ := b1e45418 X0
           have i₂ := b1e26 (M.op X0 x)
           grind)
        | exact superpose b1e26 b1e45418
        | exact resolve b1e45418 b1e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e45418
      have b1e101467 : ∀ X0 : G, (M.op y X0) = (k y (M.op y X0)) ∨ (M.op X0 y) = (M.op y X0) ∨ (M.op X0 x) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b1e5331 y X0
           have i₂ := b1e36483 X0
           grind)
        | exact superpose b1e36483 b1e5331
        | (have j1 := b1e36483 X0
           grind)
        | exact resolve b1e5331 b1e36483
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5331 b1e36483
      have b1e101498 : ∀ X0 : G, (M.op X0 x) = (M.op y X0) ∨ (M.op y X0) = (k y (M.op y X0)) ∨ (M.op X0 x) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b1e101467 X0
           have i₂ := b1e26 X0
           grind)
        | exact superpose b1e26 b1e101467
        | (have j0 := b1e101467 X0
           grind)
        | exact resolve b1e101467 b1e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e101467
      have b1e101506 : ∀ X0 : G, (M.op y X0) = (k y (M.op y X0)) ∨ (M.op X0 x) = (k y X0) := by
        intro X0
        first
        | (have j0 := b1e101498 X0
           have j1 := b1e20468 X0
           grind)
        | (have r₁ := b1e101498 X0
           have r₂ := b1e20468 X0
           grind)
        | exact resolve b1e101498 b1e20468
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e101498
      have b1e121959 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e13 X0 X1
           have i₂ := b1e41965 X0 X1 X2
           grind)
        | (have i₁ := b1e13 X0 X0
           have i₂ := b1e41965 X0 X1 X2
           grind)
        | exact superpose b1e41965 b1e13
        | (have j0 := b1e13 X0 X0
           have j1 := b1e41965 X0 X1 X2
           grind)
        | (have r₁ := b1e13 X0 X1
           have r₂ := b1e41965 X0 X1 X2
           grind)
        | (have r₁ := b1e13 X1 X1
           have r₂ := b1e41965 X1 X1 X2
           grind)
        | (have r₁ := b1e13 (k X0 X1) X0
           have r₂ := b1e41965 X0 X1 (k X0 X1)
           grind)
        | exact resolve b1e13 b1e41965
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e41965
      have b1e122097 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have j0 := b1e121959 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e121959
      have b1e122269 : ∀ X0 X1 : G, (τ (M.op (M.op X0 (σ (M.op X1 X1))) (σ X1))) = (k (τ (M.op X0 (σ (M.op X1 X1)))) (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e45546 X0 (M.op X1 X1)
           have i₂ := b1e261 X1 (M.op X0 (σ (M.op X1 X1)))
           grind)
        | exact superpose b1e261 b1e45546
        | exact resolve b1e45546 b1e261
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e122272 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 (σ X1))) X2) = (M.op (k (τ (M.op X0 (σ X1))) X1) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e2328 X0 (σ X1) X2
           have i₂ := b1e45546 X0 X1
           grind)
        | exact superpose b1e45546 b1e2328
        | exact resolve b1e2328 b1e45546
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2328
      have b1e122291 : ∀ X0 X1 : G, (τ (M.op (M.op X0 (σ X1)) (σ X1))) = (k (τ (M.op X0 (σ X1))) (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e122269 X1 X0
           have i₂ := b1e261 X0 X1
           grind)
        | exact superpose b1e261 b1e122269
        | exact resolve b1e122269 b1e261
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e261 b1e122269
      have b1e122304 : ∀ X0 X1 : G, (k (τ (M.op X0 (σ X1))) X1) = (k (τ (M.op X0 (σ X1))) (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e122291 X0 X1
           have i₂ := b1e45546 X0 X1
           grind)
        | exact superpose b1e45546 b1e122291
        | exact resolve b1e122291 b1e45546
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e122291
      have b1e128256 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
        intro X0 X1
        first
        | (have j0 := b1e6245 X0 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6245
      have b1e128257 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
        intro X0 X1
        first
        | (have j0 := b1e128256 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e128256
      have b1e128458 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e36047 (M.op X0 X1) X0
           have i₂ := b1e128257 X0 X1
           grind)
        | exact superpose b1e128257 b1e36047
        | (have j0 := b1e36047 (M.op X0 X1) X0
           grind)
        | exact resolve b1e36047 b1e128257
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e36047 b1e128257
      have b1e128510 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have j0 := b1e128458 X0 X1
           have j1 := b1e20384 X0 X1 X0
           grind)
        | (have r₁ := b1e128458 x X1
           have r₂ := b1e20384 x X1 x
           grind)
        | exact resolve b1e128458 b1e20384
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20384 b1e128458
      have b1e132362 : ∀ X0 X1 : G, (k (σ X0) X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (k (σ X0) X1) = (M.op (σ (τ X1)) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e20175 (τ X0) X1
           have i₂ := b1e21 X0 X1
           grind)
        | exact superpose b1e21 b1e20175
        | exact resolve b1e20175 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21 b1e20175
      have b1e132367 : ∀ X0 X1 : G, (k (σ X0) X1) ≠ (M.op X1 X1) ∨ (k (σ X0) X1) = (M.op (σ (τ X1)) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e132362 X0 X1
           have i₂ := b1e185 X1
           grind)
        | exact superpose b1e185 b1e132362
        | (have j0 := b1e132362 X0 X1
           grind)
        | exact resolve b1e132362 b1e185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e185 b1e132362
      have b1e132373 : ∀ X0 X1 : G, (k (σ X0) X1) ≠ (M.op X1 X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e132367 X0 X1
           have i₂ := b1e12 X1
           grind)
        | exact superpose b1e12 b1e132367
        | (have j0 := b1e132367 X0 X1
           grind)
        | exact resolve b1e132367 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e132367
      have b1e134301 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y X0) y) ∨ (M.op X0 x) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b1e128510 y X0
           have i₂ := b1e101506 X0
           grind)
        | exact superpose b1e101506 b1e128510
        | (have j1 := b1e101506 X0
           grind)
        | exact resolve b1e128510 b1e101506
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e101506
      have b1e134309 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y X0) x) ∨ (M.op X0 x) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b1e134301 X0
           have i₂ := b1e26 (M.op y X0)
           grind)
        | exact superpose b1e26 b1e134301
        | (have j0 := b1e134301 X0
           grind)
        | exact resolve b1e134301 b1e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e26 b1e134301
      have b1e135394 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X2 (k X0 X1)) ∨ (M.op X3 X0) = (M.op X3 (k X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e25 X0 X2 X0
           have i₂ := b1e122097 X0 X1 X3
           grind)
        | exact superpose b1e122097 b1e25
        | (have j1 := b1e122097 X0 X1 X2
           grind)
        | exact resolve b1e25 b1e122097
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e122097
      have b1e139762 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (k (M.op X0 (σ x)) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e14502 (σ x) X0
           have i₂ := b1e60 x
           grind)
        | exact superpose b1e60 b1e14502
        | (have j0 := b1e14502 (σ x) X0
           grind)
        | (have r₁ := b1e14502 (σ x) x
           have r₂ := b1e60 x
           grind)
        | exact resolve b1e14502 b1e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e14502
      have b1e139763 : ∀ X0 : G, (M.op (σ y) (σ x)) = (k (M.op X0 (σ x)) (σ y)) := by
        intro X0
        first
        | (have j0 := b1e139762 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e139762
      have b1e139764 : ∀ X0 : G, (σ (M.op x x)) = (k (M.op X0 (σ x)) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e139763 X0
           have i₂ := b1e14515
           grind)
        | exact superpose b1e14515 b1e139763
        | exact resolve b1e139763 b1e14515
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e14515 b1e139763
      have b1e139909 : ∀ X0 : G, (τ (σ (M.op x x))) = (k (τ (M.op X0 (σ x))) y) := by
        intro X0
        first
        | (have i₁ := b1e183 (M.op X0 (σ x)) y
           have i₂ := b1e139764 X0
           grind)
        | exact superpose b1e139764 b1e183
        | exact resolve b1e183 b1e139764
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e183 b1e139764
      have b1e139914 : ∀ X0 : G, (M.op x x) = (k (τ (M.op X0 (σ x))) y) := by
        intro X0
        first
        | (have i₁ := b1e139909 X0
           have i₂ := b1e11 (M.op x x)
           grind)
        | exact superpose b1e11 b1e139909
        | exact resolve b1e139909 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e139909
      have b1e140092 : ∀ X0 : G, (M.op x x) = (k (k (τ (M.op X0 (σ x))) x) y) := by
        intro X0
        first
        | (have i₁ := b1e139914 (M.op X0 (σ x))
           have i₂ := b1e45546 X0 x
           grind)
        | exact superpose b1e45546 b1e139914
        | exact resolve b1e139914 b1e45546
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e144394 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e132373 (τ X0) X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e132373
        | exact resolve b1e132373 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e132373
      have b1e144414 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e144394 X0 X1
           have i₂ := b1e84 X0 X1
           grind)
        | exact superpose b1e84 b1e144394
        | (have j0 := b1e144394 X0 X1
           have j1 := b1e84 X0 X1
           grind)
        | (have r₁ := b1e144394 X0 X0
           have r₂ := b1e84 X0 X0
           grind)
        | exact resolve b1e144394 b1e84
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e84 b1e144394
      have b1e144523 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b1e144414 X0 X1
           have j1 := b1e225 X0 X1
           grind)
        | (have r₁ := b1e144414 X0 X1
           have r₂ := b1e225 X0 X1
           grind)
        | (have r₁ := b1e144414 X0 X0
           have r₂ := b1e225 X0 X0
           grind)
        | exact resolve b1e144414 b1e225
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e225 b1e144414
      have b1e144656 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e144523 (σ X0) X1
           have i₂ := b1e60 X0
           grind)
        | exact superpose b1e60 b1e144523
        | (have j0 := b1e144523 (σ X0) X1
           grind)
        | exact resolve b1e144523 b1e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e144523
      have b1e151469 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e144656 X1 (σ X0)
           have i₂ := b1e60 X0
           grind)
        | exact superpose b1e60 b1e144656
        | (have j0 := b1e144656 X1 (σ X0)
           grind)
        | (have r₁ := b1e144656 X0 (σ X0)
           have r₂ := b1e60 X0
           grind)
        | exact resolve b1e144656 b1e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e144656
      have b1e151479 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e151469 X0 X1
           have i₂ := b1e15 X1 X0
           grind)
        | exact superpose b1e15 b1e151469
        | (have j0 := b1e151469 X0 X1
           grind)
        | exact resolve b1e151469 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e151469
      have b1e167859 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 (k X1 X2)) := by
        intro X0 X1 X2
        first
        | (have j0 := b1e135394 X1 X2 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e135394
      have b1e167860 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (k X1 X2)) := by
        intro X0 X1 X2
        first
        | (have j0 := b1e167859 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e167859
      have b1e168321 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e167860 X2 (σ X0) (σ X1)
           have i₂ := b1e15 X0 X1
           grind)
        | exact superpose b1e15 b1e167860
        | exact resolve b1e167860 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e168365 : ∀ X0 X1 : G, (M.op X0 (M.op x x)) = (M.op X0 (τ (M.op X1 (σ x)))) := by
        intro X0 X1
        first
        | (have i₁ := b1e167860 X0 (τ (M.op X1 (σ x))) y
           have i₂ := b1e139914 X1
           grind)
        | exact superpose b1e139914 b1e167860
        | exact resolve b1e167860 b1e139914
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e168658 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) X2) = (M.op (M.op (k X0 X1) X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e27 (k X0 X1) X2
           have i₂ := b1e167860 (k X0 X1) X0 X1
           grind)
        | exact superpose b1e167860 b1e27
        | exact resolve b1e27 b1e167860
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e169446 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (τ (M.op X1 (σ x)))) := by
        intro X0 X1
        first
        | (have i₁ := b1e168365 X0 X1
           have i₂ := b1e25 x X0 x
           grind)
        | exact superpose b1e25 b1e168365
        | exact resolve b1e168365 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e168365
      have b1e170314 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ X0)) = (σ (M.op (k X0 X1) (k X0 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e60 (k X0 X1)
           have i₂ := b1e168321 X0 X1 (σ (k X0 X1))
           grind)
        | exact superpose b1e168321 b1e60
        | exact resolve b1e60 b1e168321
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e168321
      have b1e170447 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ X0)) = (σ (M.op (k X0 X1) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e170314 X0 X1
           have i₂ := b1e167860 (k X0 X1) X0 X1
           grind)
        | exact superpose b1e167860 b1e170314
        | exact resolve b1e170314 b1e167860
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e167860 b1e170314
      have b1e171772 : ∀ X0 X1 : G, (M.op (τ (M.op X0 (σ x))) X1) = (M.op (M.op (τ (M.op X0 (σ x))) x) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e27 (τ (M.op X0 (σ x))) X1
           have i₂ := b1e169446 (τ (M.op X0 (σ x))) X0
           grind)
        | exact superpose b1e169446 b1e27
        | exact resolve b1e27 b1e169446
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e171860 : ∀ X0 : G, (M.op (τ (M.op X0 (σ x))) x) = (τ (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) := by
        intro X0
        first
        | (have i₁ := b1e617 (M.op X0 (σ x))
           have i₂ := b1e169446 (τ (M.op X0 (σ x))) X0
           grind)
        | exact superpose b1e169446 b1e617
        | exact resolve b1e617 b1e169446
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e617
      have b1e171935 : ∀ X0 : G, (M.op (τ (M.op X0 (σ x))) x) = (τ (M.op (M.op X0 (σ x)) (σ x))) := by
        intro X0
        first
        | (have i₁ := b1e171860 X0
           have i₂ := b1e25 (σ x) (M.op X0 (σ x)) X0
           grind)
        | exact superpose b1e25 b1e171860
        | exact resolve b1e171860 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25 b1e171860
      have b1e172042 : ∀ X0 : G, (M.op (τ (M.op X0 (σ x))) x) = (k (τ (M.op X0 (σ x))) x) := by
        intro X0
        first
        | (have i₁ := b1e171935 X0
           have i₂ := b1e45546 X0 x
           grind)
        | exact superpose b1e45546 b1e171935
        | exact resolve b1e171935 b1e45546
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e45546 b1e171935
      have b1e180705 : ∀ X0 : G, (M.op x x) = (k (τ (σ (M.op (k x X0) x))) y) := by
        intro X0
        first
        | (have i₁ := b1e139914 (σ (k x X0))
           have i₂ := b1e170447 x X0
           grind)
        | exact superpose b1e170447 b1e139914
        | exact resolve b1e139914 b1e170447
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e139914
      have b1e180742 : ∀ X0 : G, (M.op x x) = (k (M.op (k x X0) x) y) := by
        intro X0
        first
        | (have i₁ := b1e180705 X0
           have i₂ := b1e11 (M.op (k x X0) x)
           grind)
        | exact superpose b1e11 b1e180705
        | exact resolve b1e180705 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e180705
      have b1e180817 : ∀ X0 : G, (M.op x x) = (M.op (M.op (k x X0) x) x) := by
        intro X0
        first
        | (have i₁ := b1e180742 X0
           have i₂ := b1e45629 (k x X0)
           grind)
        | exact superpose b1e45629 b1e180742
        | exact resolve b1e180742 b1e45629
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e180742
      have b1e180851 : ∀ X0 : G, (M.op x x) = (M.op (k x X0) x) := by
        intro X0
        first
        | (have i₁ := b1e180817 X0
           have i₂ := b1e168658 x X0 x
           grind)
        | exact superpose b1e168658 b1e180817
        | exact resolve b1e180817 b1e168658
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e180817
      have b1e180914 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op x X0) x) x) := by
        intro X0
        first
        | (have i₁ := b1e180851 (M.op x X0)
           have i₂ := b1e128510 x X0
           grind)
        | exact superpose b1e128510 b1e180851
        | exact resolve b1e180851 b1e128510
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e181123 : ∀ X0 X1 : G, (M.op (M.op x x) X1) = (M.op (k x X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e168658 x X0 X1
           have i₂ := b1e180851 X0
           grind)
        | exact superpose b1e180851 b1e168658
        | exact resolve b1e168658 b1e180851
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e168658 b1e180851
      have b1e181516 : ∀ X0 X1 : G, (M.op x X1) = (M.op (k x X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e181123 X0 X1
           have i₂ := b1e27 x X1
           grind)
        | exact superpose b1e27 b1e181123
        | exact resolve b1e181123 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e181123
      have b1e182047 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X0) x) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e181516 (M.op x X0) X1
           have i₂ := b1e128510 x X0
           grind)
        | exact superpose b1e128510 b1e181516
        | exact resolve b1e181516 b1e128510
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e181516
      have b1e183786 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) X1) = (M.op (σ (M.op (M.op x X0) x)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e1473 (M.op x X0) x X1
           have i₂ := b1e180914 X0
           grind)
        | exact superpose b1e180914 b1e1473
        | exact resolve b1e1473 b1e180914
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1473 b1e180914
      have b1e184139 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ (M.op (M.op x X0) x)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e183786 X0 X1
           have i₂ := b1e256 x X1
           grind)
        | exact superpose b1e256 b1e183786
        | exact resolve b1e183786 b1e256
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e183786
      have b1e199768 : ∀ X0 : G, (M.op x x) = (k (M.op (τ (M.op X0 (σ x))) x) y) := by
        intro X0
        first
        | (have i₁ := b1e140092 X0
           have i₂ := b1e172042 X0
           grind)
        | exact superpose b1e172042 b1e140092
        | exact resolve b1e140092 b1e172042
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e140092 b1e172042
      have b1e199792 : ∀ X0 : G, (M.op x x) = (M.op (M.op (τ (M.op X0 (σ x))) x) x) := by
        intro X0
        first
        | (have i₁ := b1e199768 X0
           have i₂ := b1e45629 (τ (M.op X0 (σ x)))
           grind)
        | exact superpose b1e45629 b1e199768
        | exact resolve b1e199768 b1e45629
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e45629 b1e199768
      have b1e199806 : ∀ X0 : G, (M.op x x) = (M.op (τ (M.op X0 (σ x))) x) := by
        intro X0
        first
        | (have i₁ := b1e199792 X0
           have i₂ := b1e171772 X0 x
           grind)
        | exact superpose b1e171772 b1e199792
        | exact resolve b1e199792 b1e171772
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e171772 b1e199792
      have b1e200311 : ∀ X0 : G, (k (τ (M.op X0 (σ x))) (M.op x x)) = (M.op (M.op x x) (τ (M.op X0 (σ x)))) := by
        intro X0
        first
        | (have i₁ := b1e128510 (τ (M.op X0 (σ x))) x
           have i₂ := b1e199806 X0
           grind)
        | exact superpose b1e199806 b1e128510
        | exact resolve b1e128510 b1e199806
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e128510 b1e199806
      have b1e200366 : ∀ X0 : G, (M.op x (τ (M.op X0 (σ x)))) = (k (τ (M.op X0 (σ x))) (M.op x x)) := by
        intro X0
        first
        | (have i₁ := b1e200311 X0
           have i₂ := b1e27 x (τ (M.op X0 (σ x)))
           grind)
        | exact superpose b1e27 b1e200311
        | exact resolve b1e200311 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e200311
      have b1e200415 : ∀ X0 : G, (M.op x (τ (M.op X0 (σ x)))) = (k (τ (M.op X0 (σ x))) x) := by
        intro X0
        first
        | (have i₁ := b1e200366 X0
           have i₂ := b1e122304 X0 x
           grind)
        | exact superpose b1e122304 b1e200366
        | exact resolve b1e200366 b1e122304
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e122304 b1e200366
      have b1e200421 : ∀ X0 : G, (M.op x x) = (k (τ (M.op X0 (σ x))) x) := by
        intro X0
        first
        | (have i₁ := b1e200415 X0
           have i₂ := b1e169446 x X0
           grind)
        | exact superpose b1e169446 b1e200415
        | exact resolve b1e200415 b1e169446
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e200415
      have b1e200657 : ∀ X0 X1 : G, (M.op (M.op x x) X1) = (M.op (τ (M.op X0 (σ x))) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e122272 X0 x X1
           have i₂ := b1e200421 X0
           grind)
        | exact superpose b1e200421 b1e122272
        | exact resolve b1e122272 b1e200421
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e122272 b1e200421
      have b1e200693 : ∀ X0 X1 : G, (M.op x X1) = (M.op (τ (M.op X0 (σ x))) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e200657 X0 X1
           have i₂ := b1e27 x X1
           grind)
        | exact superpose b1e27 b1e200657
        | exact resolve b1e200657 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27 b1e200657
      have b1e201075 : ∀ X0 X1 : G, (M.op (σ (τ (M.op X0 (σ x)))) X1) = (M.op (σ (M.op x (τ (M.op X0 (σ x))))) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e256 (τ (M.op X0 (σ x))) X1
           have i₂ := b1e200693 X0 (τ (M.op X0 (σ x)))
           grind)
        | exact superpose b1e200693 b1e256
        | exact resolve b1e256 b1e200693
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e200693
      have b1e201608 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) X1) = (M.op (σ (τ (M.op X0 (σ x)))) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e201075 X0 X1
           have i₂ := b1e169446 x X0
           grind)
        | exact superpose b1e169446 b1e201075
        | exact resolve b1e201075 b1e169446
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e169446 b1e201075
      have b1e201739 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) X1) = (M.op (M.op X0 (σ x)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e201608 X0 X1
           have i₂ := b1e12 (M.op X0 (σ x))
           grind)
        | exact superpose b1e12 b1e201608
        | exact resolve b1e201608 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e201608
      have b1e201753 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op X0 (σ x)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e201739 X0 X1
           have i₂ := b1e256 x X1
           grind)
        | exact superpose b1e256 b1e201739
        | exact resolve b1e201739 b1e256
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e256 b1e201739
      have b1e202130 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (M.op X0 X0)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
        intro X0
        first
        | (have i₁ := b1e739 X0 x
           have i₂ := b1e201753 (σ X0) (σ x)
           grind)
        | exact superpose b1e201753 b1e739
        | (have j0 := b1e739 X0 x
           grind)
        | exact resolve b1e739 b1e201753
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e739
      have b1e202149 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (σ x) x) X0) := by
        intro X0
        first
        | (have i₁ := b1e182047 (σ x) X0
           have i₂ := b1e201753 x x
           grind)
        | exact superpose b1e201753 b1e182047
        | exact resolve b1e182047 b1e201753
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e182047
      have b1e202151 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op (σ x) x)) X0) := by
        intro X0
        first
        | (have i₁ := b1e184139 (σ x) X0
           have i₂ := b1e201753 x x
           grind)
        | exact superpose b1e201753 b1e184139
        | exact resolve b1e184139 b1e201753
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e184139
      have b1e202164 : (M.op (σ x) x) = (M.op y (σ x)) ∨ (M.op (σ x) x) = (k y (σ x)) := by
        first
        | (have i₁ := b1e134309 (σ x)
           have i₂ := b1e201753 y x
           grind)
        | exact superpose b1e201753 b1e134309
        | (have j0 := b1e134309 (σ x)
           grind)
        | exact resolve b1e134309 b1e201753
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e134309 b1e201753
      have b1e202681 : (M.op (σ x) x) = (k y (σ x)) := by
        first
        | (have j1 := b1e20468 (σ x)
           grind)
        | (have r₁ := b1e202164
           have r₂ := b1e20468 (σ x)
           grind)
        | exact resolve b1e202164 b1e20468
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20468 b1e202164
      have b1e202682 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op X0 X0)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
        intro X0
        first
        | (have i₁ := b1e202130 X0
           have i₂ := b1e60 x
           grind)
        | exact superpose b1e60 b1e202130
        | (have j0 := b1e202130 X0
           grind)
        | exact resolve b1e202130 b1e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e60 b1e202130
      have b1e202812 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
        intro X0
        first
        | (have j0 := b1e202682 X0
           have j1 := b1e151479 x X0
           grind)
        | (have r₁ := b1e202682 x
           have r₂ := b1e151479 x x
           grind)
        | (have r₁ := b1e202682 X0
           have r₂ := b1e151479 X0 x
           grind)
        | exact resolve b1e202682 b1e151479
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e151479 b1e202682
      have b1e203044 : (σ (M.op (M.op (σ x) x) y)) = (M.op (σ (M.op (σ x) x)) (σ y)) := by
        first
        | (have i₁ := b1e170447 y (σ x)
           have i₂ := b1e202681
           grind)
        | exact superpose b1e202681 b1e170447
        | exact resolve b1e170447 b1e202681
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e170447 b1e202681
      have b1e203058 : (M.op (σ x) (σ y)) = (σ (M.op (M.op (σ x) x) y)) := by
        first
        | (have i₁ := b1e203044
           have i₂ := b1e202151 (σ y)
           grind)
        | exact superpose b1e202151 b1e203044
        | exact resolve b1e203044 b1e202151
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e202151 b1e203044
      have b1e203101 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e203058
           have i₂ := b1e202149 y
           grind)
        | exact superpose b1e202149 b1e203058
        | exact resolve b1e203058 b1e202149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e202149 b1e203058
      have b1e203117 : (σ (M.op x y)) = (σ (k y x)) := by
        first
        | (have i₁ := b1e203101
           have i₂ := b1e202812 y
           grind)
        | exact superpose b1e202812 b1e203101
        | exact resolve b1e203101 b1e202812
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e202812 b1e203101
      have b1e203127 : (σ (M.op x y)) = (σ (M.op y x)) := by
        first
        | (have i₁ := b1e203117
           have i₂ := b1e1871
           grind)
        | exact superpose b1e1871 b1e203117
        | exact resolve b1e203117 b1e1871
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1871 b1e203117
      have b1e203132 : (σ (M.op x x)) = (σ (M.op y x)) := by
        first
        | (have i₁ := b1e203127
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e203127
        | exact resolve b1e203127 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e203127
      have b1e203134 : False := by grind
      exact b1e203134
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X2 X1)) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b2e17 : (M.op x y) ≠ (M.op x x) := by grind
      have b2e18 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e16
        | exact resolve b2e16 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
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
      have b2e21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X1 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e15
        | exact resolve b2e15 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e22 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 X1)) = (M.op (M.op X0 X0) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 (M.op X0 X0) X1 X2
           have i₂ := b2e10 X0 X0 X0
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X2 (M.op X3 X1) (M.op X0 X0)
           have i₂ := b2e10 X0 X1 X3
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e24 : ∀ X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op X3 X1)) := by
        intro X1 X2 X3
        first
        | (have i₁ := b2e23 x X1 X2 X3
           have i₂ := b2e10 X2 X1 x
           grind)
        | exact superpose b2e10 b2e23
        | exact resolve b2e23 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e23
      have b2e25 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e22 X0 X1 x
           have i₂ := b2e10 X0 X1 x
           grind)
        | exact superpose b2e10 b2e22
        | exact resolve b2e22 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e22
      have b2e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X1) (M.op X3 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 (M.op X0 X1) X2 X3
           have i₂ := b2e24 X1 (M.op X0 X1) X0
           grind)
        | exact superpose b2e24 b2e10
        | exact resolve b2e10 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e33 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X1) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e29 X0 X1 X2 x
           have i₂ := b2e24 X2 (M.op (M.op X0 X1) X1) x
           grind)
        | exact superpose b2e24 b2e29
        | exact resolve b2e29 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e29
      have b2e37 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) := by
        intro X0
        first
        | (have i₁ := b2e10 X0 (σ y) (σ x)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e38 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e37 X0
           have i₂ := b2e10 X0 (σ x) (σ x)
           grind)
        | exact superpose b2e10 b2e37
        | exact resolve b2e37 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e37
      have b2e52 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e13 (M.op X0 X0) (M.op X2 X1)
           have i₂ := b2e10 X0 X1 X2
           grind)
        | exact superpose b2e10 b2e13
        | (have j0 := b2e13 (M.op X0 X0) (M.op X2 X1)
           grind)
        | exact resolve b2e13 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e53 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e13 X0 (M.op X2 X1)
           have i₂ := b2e24 X1 X0 X2
           grind)
        | exact superpose b2e24 b2e13
        | (have j0 := b2e13 X0 X1
           grind)
        | (have r₁ := b2e13 (M.op x X1) X1
           have r₂ := b2e24 X1 (M.op x X1) x
           grind)
        | (have r₁ := b2e13 X1 (M.op x X1)
           have r₂ := b2e24 X1 X1 x
           grind)
        | exact resolve b2e13 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e54 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b2e13 (σ x) (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e13
        | (have j0 := b2e13 (σ x) (σ x)
           grind)
        | (have r₁ := b2e13 (σ x) (σ y)
           have r₂ := b2e18
           grind)
        | exact resolve b2e13 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e57 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e13 (M.op x X1) X1
           have i₂ := b2e24 X1 (M.op x X1) x
           grind)
        | exact superpose b2e24 b2e13
        | (have r₁ := b2e13 (M.op x X1) X1
           have r₂ := b2e24 X1 (M.op x X1) x
           grind)
        | (have r₁ := b2e13 X1 (M.op x X1)
           have r₂ := b2e24 X1 X1 x
           grind)
        | exact resolve b2e13 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b2e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e60 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b2e54
      have b2e64 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b2e60
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e60
        | exact resolve b2e60 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e60
      have b2e65 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e52 X0 X1 X2
           have i₂ := b2e10 X0 X0 X0
           grind)
        | exact superpose b2e10 b2e52
        | (have j0 := b2e52 X0 X1 X2
           grind)
        | (have r₁ := b2e52 X1 X1 X2
           have r₂ := b2e10 X1 X1 X1
           grind)
        | exact resolve b2e52 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e52
      have b2e68 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e65 X0 X1 X2
           have i₂ := b2e10 X0 X0 X0
           grind)
        | exact superpose b2e10 b2e65
        | (have j0 := b2e65 X0 X1 X2
           grind)
        | exact resolve b2e65 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e65
      have b2e71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b2e15 X0 X0
           have i₂ := b2e59 (σ X0)
           grind)
        | exact superpose b2e59 b2e15
        | exact resolve b2e15 b2e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b2e71 X0
           have i₂ := b2e59 X0
           grind)
        | exact superpose b2e59 b2e71
        | exact resolve b2e71 b2e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e71
      have b2e82 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e13 X0 X1
           have i₂ := b2e14 X0 X1
           grind)
        | (have i₁ := b2e13 X0 X0
           have i₂ := b2e14 X0 X1
           grind)
        | exact superpose b2e14 b2e13
        | (have j0 := b2e13 X0 X0
           have j1 := b2e14 X0 X1
           grind)
        | (have r₁ := b2e13 X0 X1
           have r₂ := b2e14 X0 X1
           grind)
        | (have r₁ := b2e13 X1 X1
           have r₂ := b2e14 X1 X1
           grind)
        | exact resolve b2e13 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e88 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e13 X1 X1
           have i₂ := b2e14 X1 X1
           grind)
        | (have i₁ := b2e13 X0 X1
           have i₂ := b2e14 X0 X1
           grind)
        | exact superpose b2e14 b2e13
        | (have j1 := b2e14 X0 X1
           grind)
        | (have r₁ := b2e13 X0 X1
           have r₂ := b2e14 X0 X1
           grind)
        | (have r₁ := b2e13 X1 X1
           have r₂ := b2e14 X1 X1
           grind)
        | exact resolve b2e13 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e89 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) X2) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e25 X0 X2
           have i₂ := b2e14 X0 X1
           grind)
        | (have i₁ := b2e25 X1 X1
           have i₂ := b2e14 X1 X1
           grind)
        | exact superpose b2e14 b2e25
        | (have j1 := b2e14 X0 X1
           grind)
        | exact resolve b2e25 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e93 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 X1)) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 X2 X0 X0
           have i₂ := b2e14 X0 X1
           grind)
        | (have i₁ := b2e10 X0 X1 X0
           have i₂ := b2e14 X0 X1
           grind)
        | exact superpose b2e14 b2e10
        | (have j1 := b2e14 X0 X1
           grind)
        | exact resolve b2e10 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e98 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X1 X0
           have i₂ := b2e14 (σ X1) (σ X0)
           grind)
        | exact superpose b2e14 b2e15
        | (have j1 := b2e14 (σ X1) (σ X0)
           grind)
        | exact resolve b2e15 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e100 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b2e82 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e82
      have b2e101 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e98 X0 X1
           have i₂ := b2e72 X1
           grind)
        | exact superpose b2e72 b2e98
        | (have j0 := b2e98 X0 X1
           grind)
        | exact resolve b2e98 b2e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e98
      have b2e105 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e93 X0 X1 X2
           have i₂ := b2e10 X2 X1 X0
           grind)
        | exact superpose b2e10 b2e93
        | (have j0 := b2e93 X0 X1 X2
           grind)
        | exact resolve b2e93 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e93
      have b2e149 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b2e20 X0 (τ X0)
           have i₂ := b2e59 (τ X0)
           grind)
        | exact superpose b2e59 b2e20
        | exact resolve b2e20 b2e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e153 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e11 (k (τ X0) X1)
           have i₂ := b2e20 X0 X1
           grind)
        | exact superpose b2e20 b2e11
        | exact resolve b2e11 b2e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e154 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b2e149 X0
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e149
        | exact resolve b2e149 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e149
      have b2e155 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b2e154 X0
           have i₂ := b2e59 X0
           grind)
        | exact superpose b2e59 b2e154
        | exact resolve b2e154 b2e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e154
      have b2e163 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e11 (k X0 (τ X1))
           have i₂ := b2e21 X1 X0
           grind)
        | exact superpose b2e21 b2e11
        | exact resolve b2e11 b2e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e169 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have i₁ := b2e19
           have i₂ := b2e64
           grind)
        | exact superpose b2e64 b2e19
        | exact resolve b2e19 b2e64
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e174 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
        first
        | (have i₁ := b2e13 (σ x) (σ x)
           have i₂ := b2e64
           grind)
        | exact superpose b2e64 b2e13
        | exact resolve b2e13 b2e64
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e177 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
      clear b2e174
      have b2e179 : (σ (k x y)) = (σ (k x x)) := by
        first
        | (have i₁ := b2e177
           have i₂ := b2e15 x x
           grind)
        | exact superpose b2e15 b2e177
        | exact resolve b2e177 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e177
      have b2e181 : (σ (k x y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b2e179
           have i₂ := b2e59 x
           grind)
        | exact superpose b2e59 b2e179
        | exact resolve b2e179 b2e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e59 b2e179
      have b2e182 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b2e169
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e169
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e169 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e183 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
        first
        | (have r₁ := b2e182
           have r₂ := b2e17
           grind)
        | exact resolve b2e182 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e182
      have b2e209 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e20 X0 X1
           have i₂ := b2e100 (τ X0) X1
           grind)
        | exact superpose b2e100 b2e20
        | (have j1 := b2e100 (τ X0) X1
           grind)
        | exact resolve b2e20 b2e100
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e20
      have b2e215 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b2e100 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e100
      have b2e218 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e209 X0 X1
           have i₂ := b2e155 X0
           grind)
        | exact superpose b2e155 b2e209
        | (have j0 := b2e209 X0 X1
           grind)
        | exact resolve b2e209 b2e155
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e209
      have b2e241 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b2e169
           have i₂ := b2e181
           grind)
        | exact superpose b2e181 b2e169
        | exact resolve b2e169 b2e181
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e169
      have b2e244 : (k x y) = (τ (σ (M.op x x))) := by
        first
        | (have i₁ := b2e11 (k x y)
           have i₂ := b2e181
           grind)
        | exact superpose b2e181 b2e11
        | exact resolve b2e11 b2e181
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e245 : (M.op x x) = (k x y) := by
        first
        | (have i₁ := b2e244
           have i₂ := b2e11 (M.op x x)
           grind)
        | exact superpose b2e11 b2e244
        | exact resolve b2e244 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e244
      have b2e275 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e13 X1 X1
           have i₂ := b2e105 X0 X1 X1
           grind)
        | (have i₁ := b2e13 X0 X1
           have i₂ := b2e105 X0 X1 X0
           grind)
        | exact superpose b2e105 b2e13
        | (have j1 := b2e105 X1 X0 X2
           grind)
        | (have r₁ := b2e13 X0 X1
           have r₂ := b2e105 X0 X1 X0
           grind)
        | (have r₁ := b2e13 X1 X0
           have r₂ := b2e105 X0 X1 X1
           grind)
        | exact resolve b2e13 b2e105
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e279 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X2) ∨ (M.op X2 X1) = (k X1 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e13 X0 X2
           have i₂ := b2e105 X1 X2 X0
           grind)
        | (have i₁ := b2e13 X2 X0
           have i₂ := b2e105 X0 X1 X2
           grind)
        | exact superpose b2e105 b2e13
        | (have j0 := b2e13 X0 X1
           have j1 := b2e105 X1 X2 X2
           grind)
        | (have r₁ := b2e13 X0 X1
           have r₂ := b2e105 X0 X1 X0
           grind)
        | (have r₁ := b2e13 X1 X0
           have r₂ := b2e105 X0 X1 X1
           grind)
        | exact resolve b2e13 b2e105
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e298 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (k (M.op X3 X2) X1) = (M.op X1 (M.op X3 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e24 X2 X0 X3
           have i₂ := b2e105 (M.op X3 X2) X1 X0
           grind)
        | (have i₁ := b2e24 X1 X2 X3
           have i₂ := b2e105 X0 (M.op X3 X1) X2
           grind)
        | exact superpose b2e105 b2e24
        | (have j1 := b2e105 X2 X1 X0
           grind)
        | exact resolve b2e24 b2e105
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e306 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X2 (σ X1)) = (M.op X2 (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e15 X1 X0
           have i₂ := b2e105 (σ X1) (σ X0) X2
           grind)
        | exact superpose b2e105 b2e15
        | (have j1 := b2e105 (σ X0) (σ X1) X2
           grind)
        | exact resolve b2e15 b2e105
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e314 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (k (M.op X3 X2) X1) ∨ (M.op X0 X1) = (M.op X0 X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e298 X0 X1 X2 X3
           have i₂ := b2e24 X2 X1 X3
           grind)
        | exact superpose b2e24 b2e298
        | (have j0 := b2e298 X0 X1 X2 X3
           grind)
        | exact resolve b2e298 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e298
      have b2e345 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b2e14 x y
           have i₂ := b2e245
           grind)
        | exact superpose b2e245 b2e14
        | (have j0 := b2e14 x y
           grind)
        | exact resolve b2e14 b2e245
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e245
      have b2e346 : (M.op x x) = (M.op y x) := by
        first
        | (have r₁ := b2e345
           have r₂ := b2e17
           grind)
        | exact resolve b2e345 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e345
      have b2e461 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b2e68 X0 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e68
      have b2e569 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e24 (σ X0) X2 (σ X1)
           have i₂ := b2e101 X1 X0
           grind)
        | exact superpose b2e101 b2e24
        | (have j1 := b2e101 X1 X0
           grind)
        | exact resolve b2e24 b2e101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e101
      have b2e697 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e72 (k X1 (τ X0))
           have i₂ := b2e21 X0 X1
           grind)
        | exact superpose b2e21 b2e72
        | exact resolve b2e72 b2e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e715 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e25 (σ X0) X1
           have i₂ := b2e72 X0
           grind)
        | exact superpose b2e72 b2e25
        | exact resolve b2e25 b2e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e725 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e24 (σ X0) X1 (σ X0)
           have i₂ := b2e72 X0
           grind)
        | exact superpose b2e72 b2e24
        | exact resolve b2e24 b2e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e904 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e153 X1 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e153
        | exact resolve b2e153 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e965 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b2e88 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e88
      have b2e1641 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (M.op (σ x) (σ x))) := by
        first
        | (have i₁ := b2e461 (σ y) (σ x)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e461
        | exact resolve b2e461 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e461
      have b2e1672 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (σ (k x y))) := by
        first
        | (have i₁ := b2e1641
           have i₂ := b2e64
           grind)
        | exact superpose b2e64 b2e1641
        | exact resolve b2e1641 b2e64
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e64 b2e1641
      have b2e1700 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (σ (M.op x x))) := by
        first
        | (have i₁ := b2e1672
           have i₂ := b2e181
           grind)
        | exact superpose b2e181 b2e1672
        | exact resolve b2e1672 b2e181
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e181 b2e1672
      have b2e1717 : (σ (M.op y y)) = (k (σ (M.op y y)) (σ (M.op x x))) := by
        first
        | (have i₁ := b2e1700
           have i₂ := b2e72 y
           grind)
        | exact superpose b2e72 b2e1700
        | exact resolve b2e1700 b2e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1700
      have b2e1725 : (σ (M.op y y)) = (σ (k (M.op y y) (M.op x x))) := by
        first
        | (have i₁ := b2e1717
           have i₂ := b2e15 (M.op y y) (M.op x x)
           grind)
        | exact superpose b2e15 b2e1717
        | exact resolve b2e1717 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1717
      have b2e3103 : (k (M.op y y) (M.op x x)) = (τ (σ (M.op y y))) := by
        first
        | (have i₁ := b2e11 (k (M.op y y) (M.op x x))
           have i₂ := b2e1725
           grind)
        | exact superpose b2e1725 b2e11
        | exact resolve b2e11 b2e1725
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1725
      have b2e3122 : (M.op y y) = (k (M.op y y) (M.op x x)) := by
        first
        | (have i₁ := b2e3103
           have i₂ := b2e11 (M.op y y)
           grind)
        | exact superpose b2e11 b2e3103
        | exact resolve b2e3103 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3103
      have b2e3264 : ∀ X0 : G, (M.op y y) = (M.op (M.op x x) (M.op y y)) ∨ (M.op X0 (M.op x x)) = (M.op X0 (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b2e105 (M.op y y) (M.op x x) X0
           have i₂ := b2e3122
           grind)
        | exact superpose b2e3122 b2e105
        | (have j0 := b2e105 (M.op y y) (M.op x x) X0
           grind)
        | exact resolve b2e105 b2e3122
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e105 b2e3122
      have b2e3269 : ∀ X0 : G, (M.op x y) = (M.op y y) ∨ (M.op X0 (M.op x x)) = (M.op X0 (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b2e3264 X0
           have i₂ := b2e10 x y y
           grind)
        | exact superpose b2e10 b2e3264
        | (have j0 := b2e3264 X0
           grind)
        | exact resolve b2e3264 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3264
      have b2e3281 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b2e3269 X0
           have i₂ := b2e24 y X0 y
           grind)
        | exact superpose b2e24 b2e3269
        | exact resolve b2e3269 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3269
      have b2e3293 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op x y) = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b2e3281 X0
           have i₂ := b2e24 x X0 x
           grind)
        | exact superpose b2e24 b2e3281
        | exact resolve b2e3281 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3281
      have b2e3369 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b2e965 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e4509 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b2e53 X0 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e4683 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op X1 (σ X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b2e163 X0 (M.op X1 (σ X0))
           have i₂ := b2e4509 (σ X0) X1
           grind)
        | exact superpose b2e4509 b2e163
        | exact resolve b2e163 b2e4509
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e163 b2e4509
      have b2e4686 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k X0 (τ (M.op X1 (σ X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b2e4683 X0 X1
           have i₂ := b2e72 X0
           grind)
        | exact superpose b2e72 b2e4683
        | exact resolve b2e4683 b2e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4683
      have b2e4711 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (M.op X1 (σ X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b2e4686 X0 X1
           have i₂ := b2e11 (M.op X0 X0)
           grind)
        | exact superpose b2e11 b2e4686
        | exact resolve b2e4686 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4686
      have b2e5149 : ∀ X0 : G, (M.op y y) = (k y (τ (M.op X0 (σ x)))) := by
        intro X0
        first
        | (have i₁ := b2e4711 y X0
           have i₂ := b2e38 X0
           grind)
        | exact superpose b2e38 b2e4711
        | exact resolve b2e4711 b2e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4711
      have b2e5999 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 (M.op X3 X2)) ∨ (M.op X1 X0) = (k (M.op X4 X0) X1) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e53 X1 X1 X2
           have i₂ := b2e314 X1 X1 X2 X3
           grind)
        | (have i₁ := b2e53 X2 X1 X2
           have i₂ := b2e314 X2 X1 X2 X3
           grind)
        | exact superpose b2e314 b2e53
        | (have j1 := b2e314 X0 X1 X0 X4
           grind)
        | (have r₁ := b2e53 X2 X1 X2
           have r₂ := b2e314 X2 X1 X2 X3
           grind)
        | (have r₁ := b2e53 X1 X2 X2
           have r₂ := b2e314 X1 X1 X2 X3
           grind)
        | exact resolve b2e53 b2e314
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e53
      have b2e6064 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = (k (M.op X2 (τ X0)) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e155 X0
           have i₂ := b2e314 (τ X0) X1 (τ X0) X2
           grind)
        | (have i₁ := b2e155 X0
           have i₂ := b2e314 (τ X0) (τ X0) X2 x
           grind)
        | exact superpose b2e314 b2e155
        | (have j1 := b2e314 X0 X1 (τ X0) X2
           grind)
        | exact resolve b2e155 b2e314
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e314
      have b2e7649 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X0 X1
           have i₂ := b2e218 (σ X0) X1
           grind)
        | exact superpose b2e218 b2e15
        | (have j1 := b2e218 (σ X0) X1
           grind)
        | exact resolve b2e15 b2e218
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e218
      have b2e7680 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e7649 X0 X1
           have i₂ := b2e72 X0
           grind)
        | exact superpose b2e72 b2e7649
        | (have j0 := b2e7649 X0 X1
           grind)
        | exact resolve b2e7649 b2e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e7649
      have b2e7763 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e7680 X0 X1
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e7680
        | (have j0 := b2e7680 X0 X1
           grind)
        | exact resolve b2e7680 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e7680
      have b2e14911 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y x) X0) ∨ (M.op x y) = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b2e25 y X0
           have i₂ := b2e3293 y
           grind)
        | exact superpose b2e3293 b2e25
        | exact resolve b2e25 b2e3293
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3293
      have b2e15127 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x x) X0) ∨ (M.op x y) = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b2e14911 X0
           have i₂ := b2e346
           grind)
        | exact superpose b2e346 b2e14911
        | exact resolve b2e14911 b2e346
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e14911
      have b2e15160 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ (M.op x y) = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b2e15127 X0
           have i₂ := b2e25 x X0
           grind)
        | exact superpose b2e25 b2e15127
        | exact resolve b2e15127 b2e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e15127
      have b2e15937 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have j0 := b2e15160 y
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e15160
      have b2e15938 : (M.op x y) = (M.op y y) := by grind
      clear b2e15937
      have b2e16042 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x y) X0) := by
        intro X0
        first
        | (have i₁ := b2e25 y X0
           have i₂ := b2e15938
           grind)
        | exact superpose b2e15938 b2e25
        | exact resolve b2e25 b2e15938
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e16049 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b2e215 y x
           have i₂ := b2e15938
           grind)
        | exact superpose b2e15938 b2e215
        | (have r₁ := b2e215 y x
           have r₂ := b2e15938
           grind)
        | exact resolve b2e215 b2e15938
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e215
      have b2e16056 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
        intro X0
        first
        | (have i₁ := b2e725 y X0
           have i₂ := b2e15938
           grind)
        | exact superpose b2e15938 b2e725
        | exact resolve b2e725 b2e15938
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e725
      have b2e16121 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) := by
        intro X0
        first
        | (have i₁ := b2e16056 X0
           have i₂ := b2e38 X0
           grind)
        | exact superpose b2e38 b2e16056
        | exact resolve b2e16056 b2e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16056
      have b2e23049 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b2e306 X0 X1 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e306
      have b2e23050 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e23049 X0 X1
           have i₂ := b2e72 X0
           grind)
        | exact superpose b2e72 b2e23049
        | (have j0 := b2e23049 X0 X1
           grind)
        | exact resolve b2e23049 b2e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e23049
      have b2e44555 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b2e275 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e275
      have b2e48133 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y X0) ∨ (k y X0) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b2e279 y y x
           have i₂ := b2e15938
           grind)
        | exact superpose b2e15938 b2e279
        | (have j0 := b2e279 X0 y X0
           grind)
        | exact resolve b2e279 b2e15938
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e279
      have b2e48223 : ∀ X0 : G, (M.op x y) = (k y X0) ∨ (k y X0) = (M.op X0 y) := by
        intro X0
        first
        | (have j0 := b2e48133 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e48133
      have b2e48617 : ∀ X0 : G, (M.op y y) = (M.op (τ (M.op X0 (σ x))) y) ∨ (M.op x y) = (k y (τ (M.op X0 (σ x)))) := by
        intro X0
        first
        | (have i₁ := b2e5149 X0
           have i₂ := b2e48223 (τ (M.op X0 (σ x)))
           grind)
        | exact superpose b2e48223 b2e5149
        | (have j1 := b2e48223 (τ (M.op X0 (σ x)))
           grind)
        | exact resolve b2e5149 b2e48223
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e5149 b2e48223
      have b2e48643 : ∀ X0 : G, (M.op x y) = (M.op (τ (M.op X0 (σ x))) y) ∨ (M.op x y) = (k y (τ (M.op X0 (σ x)))) := by
        intro X0
        first
        | (have i₁ := b2e48617 X0
           have i₂ := b2e15938
           grind)
        | exact superpose b2e15938 b2e48617
        | (have j0 := b2e48617 X0
           grind)
        | exact resolve b2e48617 b2e15938
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e48617
      have b2e48668 : ∀ X0 : G, (M.op x y) = (k y (τ (M.op X0 (σ x)))) := by
        intro X0
        first
        | (have j0 := b2e48643 X0
           have j1 := b2e16049 (τ (M.op X0 (σ x)))
           grind)
        | (have r₁ := b2e48643 X0
           have r₂ := b2e16049 (τ (M.op X0 (σ x)))
           grind)
        | exact resolve b2e48643 b2e16049
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16049 b2e48643
      have b2e50355 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (M.op X0 (σ x))) := by
        intro X0
        first
        | (have i₁ := b2e21 (M.op X0 (σ x)) y
           have i₂ := b2e48668 X0
           grind)
        | exact superpose b2e48668 b2e21
        | exact resolve b2e21 b2e48668
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e48668
      have b2e53501 : ∀ X0 X1 X2 : G, (M.op X2 (σ (τ X0))) = (M.op X2 (σ (τ (k X0 X1)))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e569 (τ X0) (τ X1) X2
           have i₂ := b2e904 X1 X0
           grind)
        | exact superpose b2e904 b2e569
        | (have j0 := b2e569 (τ X0) (τ X1) X2
           grind)
        | exact resolve b2e569 b2e904
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e569 b2e904
      have b2e54373 : ∀ X0 X1 X2 : G, (M.op X2 (k X0 X1)) = (M.op X2 (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e53501 X0 X1 X2
           have i₂ := b2e12 (k X0 X1)
           grind)
        | exact superpose b2e12 b2e53501
        | (have j0 := b2e53501 X0 X1 X2
           grind)
        | exact resolve b2e53501 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e53501
      have b2e54517 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (k X0 X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e54373 X0 X1 X2
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e54373
        | (have j0 := b2e54373 X0 X1 X2
           grind)
        | exact resolve b2e54373 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54373
      have b2e54594 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e54517 X0 X1 X2
           have i₂ := b2e12 X1
           grind)
        | exact superpose b2e12 b2e54517
        | (have j0 := b2e54517 X0 X1 X2
           grind)
        | exact resolve b2e54517 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54517
      have b2e54646 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e54594 X0 X1 X2
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e54594
        | (have j0 := b2e54594 X0 X1 X2
           grind)
        | exact resolve b2e54594 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54594
      have b2e54682 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e54646 X0 X1 X2
           have i₂ := b2e155 X0
           grind)
        | exact superpose b2e155 b2e54646
        | (have j0 := b2e54646 X0 X1 X2
           grind)
        | exact resolve b2e54646 b2e155
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54646
      have b2e55698 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) := by
        intro X0 X1
        first
        | (have j0 := b2e57 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e57
      have b2e55974 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = (k (M.op X0 (σ x)) (σ y)) := by
        intro X0
        first
        | (have i₁ := b2e55698 X0 (σ y)
           have i₂ := b2e38 X0
           grind)
        | exact superpose b2e38 b2e55698
        | exact resolve b2e55698 b2e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e56076 : ∀ X0 X1 : G, (τ (M.op (M.op X0 (σ X1)) (σ X1))) = (k (τ (M.op X0 (σ X1))) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e153 (M.op X0 (σ X1)) X1
           have i₂ := b2e55698 X0 (σ X1)
           grind)
        | exact superpose b2e55698 b2e153
        | exact resolve b2e153 b2e55698
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e56142 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (k (M.op X0 (σ x)) (σ y)) := by
        intro X0
        first
        | (have i₁ := b2e55974 X0
           have i₂ := b2e38 (M.op X0 (σ x))
           grind)
        | exact superpose b2e38 b2e55974
        | exact resolve b2e55974 b2e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e55974
      have b2e70123 : ∀ X0 : G, (τ (M.op (M.op X0 (σ x)) (σ x))) = (k (τ (M.op X0 (σ x))) y) := by
        intro X0
        first
        | (have i₁ := b2e153 (M.op X0 (σ x)) y
           have i₂ := b2e56142 X0
           grind)
        | exact superpose b2e56142 b2e153
        | exact resolve b2e153 b2e56142
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e153 b2e56142
      have b2e70186 : ∀ X0 : G, (k (τ (M.op X0 (σ x))) y) = (k (τ (M.op X0 (σ x))) x) := by
        intro X0
        first
        | (have i₁ := b2e70123 X0
           have i₂ := b2e56076 X0 x
           grind)
        | exact superpose b2e56076 b2e70123
        | exact resolve b2e70123 b2e56076
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e70123
      have b2e94179 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e7763 X0 X1
           have i₂ := b2e44555 X0 X1
           grind)
        | exact superpose b2e44555 b2e7763
        | (have j0 := b2e7763 X1 X0
           have j1 := b2e44555 X0 X1
           grind)
        | exact resolve b2e7763 b2e44555
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e7763 b2e44555
      have b2e94287 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b2e94179 X0 X1
           have j1 := b2e3369 X1 X0
           grind)
        | (have r₁ := b2e94179 X0 X1
           have r₂ := b2e3369 X0 X1
           grind)
        | (have r₁ := b2e94179 X1 X0
           have r₂ := b2e3369 X0 X1
           grind)
        | exact resolve b2e94179 b2e3369
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e94179
      have b2e111473 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e13 X0 X1
           have i₂ := b2e54682 X0 X1 X2
           grind)
        | (have i₁ := b2e13 X0 X0
           have i₂ := b2e54682 X0 X1 X2
           grind)
        | exact superpose b2e54682 b2e13
        | (have j0 := b2e13 X0 X0
           have j1 := b2e54682 X0 X1 X2
           grind)
        | (have r₁ := b2e13 X0 X1
           have r₂ := b2e54682 X0 X1 X2
           grind)
        | (have r₁ := b2e13 X1 X1
           have r₂ := b2e54682 X1 X1 X2
           grind)
        | (have r₁ := b2e13 (k X0 X1) X0
           have r₂ := b2e54682 X0 X1 (k X0 X1)
           grind)
        | exact resolve b2e13 b2e54682
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54682
      have b2e111663 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have j0 := b2e111473 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e111473
      have b2e113298 : ∀ X0 X1 : G, (τ (M.op (M.op X0 (σ X1)) (σ X1))) = (k (τ (M.op (M.op X0 (σ X1)) (σ X1))) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e56076 (M.op X0 (σ X1)) X1
           have i₂ := b2e33 X0 (σ X1) (σ X1)
           grind)
        | exact superpose b2e33 b2e56076
        | exact resolve b2e56076 b2e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e113329 : ∀ X0 X1 : G, (k (τ (M.op X0 (σ X1))) X1) = (k (k (τ (M.op X0 (σ X1))) X1) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e113298 X0 X1
           have i₂ := b2e56076 X0 X1
           grind)
        | exact superpose b2e56076 b2e113298
        | exact resolve b2e113298 b2e56076
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e56076 b2e113298
      have b2e127641 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k (M.op X2 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e94287 X2 (M.op x X1)
           have i₂ := b2e24 X1 X2 x
           grind)
        | exact superpose b2e24 b2e94287
        | (have j0 := b2e94287 X0 X1
           grind)
        | exact resolve b2e94287 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e94287
      have b2e130503 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X2 (k X0 X1)) ∨ (M.op X3 X0) = (M.op X3 (k X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e24 X0 X2 X0
           have i₂ := b2e111663 X0 X1 X3
           grind)
        | exact superpose b2e111663 b2e24
        | (have j1 := b2e111663 X0 X1 X2
           grind)
        | exact resolve b2e24 b2e111663
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e111663
      have b2e140241 : ∀ X0 X1 : G, (k (σ X0) X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (k (σ X0) X1) = (M.op (σ (τ X1)) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e23050 (τ X0) X1
           have i₂ := b2e21 X0 X1
           grind)
        | exact superpose b2e21 b2e23050
        | exact resolve b2e23050 b2e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e23050
      have b2e140252 : ∀ X0 X1 : G, (k (σ X0) X1) ≠ (M.op X1 X1) ∨ (k (σ X0) X1) = (M.op (σ (τ X1)) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e140241 X0 X1
           have i₂ := b2e155 X1
           grind)
        | exact superpose b2e155 b2e140241
        | (have j0 := b2e140241 X0 X1
           grind)
        | exact resolve b2e140241 b2e155
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e155 b2e140241
      have b2e140259 : ∀ X0 X1 : G, (k (σ X0) X1) ≠ (M.op X1 X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e140252 X0 X1
           have i₂ := b2e12 X1
           grind)
        | exact superpose b2e12 b2e140252
        | (have j0 := b2e140252 X0 X1
           grind)
        | exact resolve b2e140252 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e140252
      have b2e143185 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e140259 (τ X0) X1
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e140259
        | exact resolve b2e140259 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e140259
      have b2e143224 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e143185 X0 X1
           have i₂ := b2e965 X0 X1
           grind)
        | exact superpose b2e965 b2e143185
        | (have j0 := b2e143185 X0 X1
           have j1 := b2e965 X0 X1
           grind)
        | (have r₁ := b2e143185 X0 X0
           have r₂ := b2e965 X0 X0
           grind)
        | exact resolve b2e143185 b2e965
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e965 b2e143185
      have b2e143277 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b2e143224 X0 X1
           have j1 := b2e3369 X0 X1
           grind)
        | (have r₁ := b2e143224 X0 X1
           have r₂ := b2e3369 X0 X1
           grind)
        | (have r₁ := b2e143224 X1 X0
           have r₂ := b2e3369 X0 X1
           grind)
        | exact resolve b2e143224 b2e3369
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3369 b2e143224
      have b2e143358 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b2e143277 X0 y
           have i₂ := b2e15938
           grind)
        | exact superpose b2e15938 b2e143277
        | (have j0 := b2e143277 X0 y
           grind)
        | (have r₁ := b2e143277 x y
           have r₂ := b2e15938
           grind)
        | exact resolve b2e143277 b2e15938
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e143277
      have b2e144706 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (M.op X2 X0) X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e6064 (σ X0) X1 X2
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e6064
        | exact resolve b2e6064 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e6064
      have b2e144732 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (k (M.op X2 X0) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e144706 X0 X1 X2
           have i₂ := b2e72 X0
           grind)
        | exact superpose b2e72 b2e144706
        | (have j0 := b2e144706 X0 X1 X2
           grind)
        | exact resolve b2e144706 b2e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e144706
      have b2e145536 : ∀ X0 : G, (k (τ (M.op X0 (σ x))) y) = (k (k (τ (M.op X0 (σ x))) y) y) := by
        intro X0
        first
        | (have i₁ := b2e113329 X0 y
           have i₂ := b2e38 X0
           grind)
        | exact superpose b2e38 b2e113329
        | exact resolve b2e113329 b2e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e113329
      have b2e145566 : ∀ X0 : G, (k (τ (M.op X0 (σ x))) x) = (k (k (τ (M.op X0 (σ x))) x) y) := by
        intro X0
        first
        | (have i₁ := b2e145536 X0
           have i₂ := b2e70186 X0
           grind)
        | exact superpose b2e70186 b2e145536
        | exact resolve b2e145536 b2e70186
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e145536
      have b2e169966 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 (k X1 X2)) := by
        intro X0 X1 X2
        first
        | (have j0 := b2e130503 X1 X2 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e130503
      have b2e169967 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (k X1 X2)) := by
        intro X0 X1 X2
        first
        | (have j0 := b2e169966 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e169966
      have b2e170292 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e169967 X2 (σ X0) (σ X1)
           have i₂ := b2e15 X0 X1
           grind)
        | exact superpose b2e15 b2e169967
        | exact resolve b2e169967 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e170507 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) X2) = (M.op (M.op (k X0 X1) X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e25 (k X0 X1) X2
           have i₂ := b2e169967 (k X0 X1) X0 X1
           grind)
        | exact superpose b2e169967 b2e25
        | exact resolve b2e25 b2e169967
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e171674 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ X0)) = (σ (M.op (k X0 X1) (k X0 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e72 (k X0 X1)
           have i₂ := b2e170292 X0 X1 (σ (k X0 X1))
           grind)
        | exact superpose b2e170292 b2e72
        | exact resolve b2e72 b2e170292
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e171815 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ X0)) = (σ (M.op (k X0 X1) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e171674 X0 X1
           have i₂ := b2e169967 (k X0 X1) X0 X1
           grind)
        | exact superpose b2e169967 b2e171674
        | exact resolve b2e171674 b2e169967
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e171674
      have b2e178606 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ (M.op (k x X0) x))) := by
        intro X0
        first
        | (have i₁ := b2e50355 (σ (k x X0))
           have i₂ := b2e171815 x X0
           grind)
        | exact superpose b2e171815 b2e50355
        | exact resolve b2e50355 b2e171815
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50355
      have b2e178613 : ∀ X0 : G, (k (τ (σ (M.op (k x X0) x))) x) = (k (k (τ (σ (M.op (k x X0) x))) x) y) := by
        intro X0
        first
        | (have i₁ := b2e145566 (σ (k x x))
           have i₂ := b2e171815 x x
           grind)
        | exact superpose b2e171815 b2e145566
        | exact resolve b2e145566 b2e171815
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e145566
      have b2e178615 : ∀ X0 : G, (M.op (σ (k y X0)) (σ x)) = (σ (M.op (k y X0) y)) := by
        intro X0
        first
        | (have i₁ := b2e38 (σ (k y X0))
           have i₂ := b2e171815 y X0
           grind)
        | exact superpose b2e171815 b2e38
        | exact resolve b2e38 b2e171815
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e171815
      have b2e178643 : ∀ X0 : G, (k (M.op (k x X0) x) x) = (k (k (M.op (k x X0) x) x) y) := by
        intro X0
        first
        | (have i₁ := b2e178613 X0
           have i₂ := b2e11 (M.op (k x X0) x)
           grind)
        | exact superpose b2e11 b2e178613
        | exact resolve b2e178613 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e178613
      have b2e178650 : ∀ X0 : G, (σ (M.op x y)) = (σ (k y (M.op (k x X0) x))) := by
        intro X0
        first
        | (have i₁ := b2e178606 X0
           have i₂ := b2e15 y (M.op (k x X0) x)
           grind)
        | exact superpose b2e15 b2e178606
        | exact resolve b2e178606 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e178606
      have b2e178792 : ∀ X0 : G, (M.op (M.op (k x X0) x) x) = (k (M.op (M.op (k x X0) x) x) y) := by
        intro X0
        first
        | (have i₁ := b2e178643 X0
           have i₂ := b2e55698 (k x X0) x
           grind)
        | exact superpose b2e55698 b2e178643
        | exact resolve b2e178643 b2e55698
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e178643
      have b2e178896 : ∀ X0 : G, (M.op (k x X0) x) = (k (M.op (k x X0) x) y) := by
        intro X0
        first
        | (have i₁ := b2e178792 x
           have i₂ := b2e170507 x x x
           grind)
        | exact superpose b2e170507 b2e178792
        | exact resolve b2e178792 b2e170507
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e178792
      have b2e179649 : ∀ X0 : G, (M.op y x) = (M.op (k x X0) x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
        intro X0
        first
        | (have i₁ := b2e144732 x y (k x X0)
           have i₂ := b2e178896 X0
           grind)
        | exact superpose b2e178896 b2e144732
        | (have j0 := b2e144732 x y x
           grind)
        | exact resolve b2e144732 b2e178896
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e144732 b2e178896
      have b2e179676 : ∀ X0 : G, (M.op y x) = (M.op (k x X0) x) := by
        intro X0
        first
        | (have j0 := b2e179649 X0
           grind)
        | (have r₁ := b2e179649 X0
           have r₂ := b2e241
           grind)
        | exact resolve b2e179649 b2e241
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e179649
      have b2e179767 : ∀ X0 : G, (M.op x x) = (M.op (k x X0) x) := by
        intro X0
        first
        | (have i₁ := b2e179676 X0
           have i₂ := b2e346
           grind)
        | exact superpose b2e346 b2e179676
        | exact resolve b2e179676 b2e346
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e346 b2e179676
      have b2e179994 : ∀ X0 X1 : G, (M.op (M.op x x) X1) = (M.op (k x X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e170507 x X0 X1
           have i₂ := b2e179767 X0
           grind)
        | exact superpose b2e179767 b2e170507
        | exact resolve b2e170507 b2e179767
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e179767
      have b2e180220 : ∀ X0 X1 : G, (M.op x X1) = (M.op (k x X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e179994 X0 X1
           have i₂ := b2e25 x X1
           grind)
        | exact superpose b2e25 b2e179994
        | exact resolve b2e179994 b2e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e25 b2e179994
      have b2e181241 : ∀ X0 X1 : G, (M.op (σ (k x X0)) X1) = (M.op (σ (M.op x (k x X0))) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e715 (k x X0) X1
           have i₂ := b2e180220 X0 (k x X0)
           grind)
        | exact superpose b2e180220 b2e715
        | exact resolve b2e715 b2e180220
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e180220
      have b2e181952 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) X1) = (M.op (σ (k x X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e181241 X0 X1
           have i₂ := b2e169967 x x X0
           grind)
        | exact superpose b2e169967 b2e181241
        | exact resolve b2e181241 b2e169967
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e181241
      have b2e182171 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ (k x X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e181952 X0 X1
           have i₂ := b2e715 x X1
           grind)
        | exact superpose b2e715 b2e181952
        | exact resolve b2e181952 b2e715
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e715 b2e181952
      have b2e185588 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (k (σ x) X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e182171 (τ X0) X1
           have i₂ := b2e21 X0 x
           grind)
        | exact superpose b2e21 b2e182171
        | exact resolve b2e182171 b2e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21 b2e182171
      have b2e197997 : ∀ X0 : G, (k (τ (σ (M.op (k y X0) y))) y) = (k (τ (σ (M.op (k y X0) y))) x) := by
        intro X0
        first
        | (have i₁ := b2e70186 (σ (k y X0))
           have i₂ := b2e178615 X0
           grind)
        | exact superpose b2e178615 b2e70186
        | exact resolve b2e70186 b2e178615
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e178615
      have b2e198035 : ∀ X0 : G, (k (M.op (k y X0) y) y) = (k (M.op (k y X0) y) x) := by
        intro X0
        first
        | (have i₁ := b2e197997 X0
           have i₂ := b2e11 (M.op (k y X0) y)
           grind)
        | exact superpose b2e11 b2e197997
        | exact resolve b2e197997 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e197997
      have b2e198096 : ∀ X0 : G, (k (M.op (k y X0) y) x) = (M.op (M.op (k y X0) y) y) := by
        intro X0
        first
        | (have i₁ := b2e198035 X0
           have i₂ := b2e55698 (k y X0) y
           grind)
        | exact superpose b2e55698 b2e198035
        | exact resolve b2e198035 b2e55698
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e198035
      have b2e198141 : ∀ X0 : G, (M.op (k y X0) y) = (k (M.op (k y X0) y) x) := by
        intro X0
        first
        | (have i₁ := b2e198096 X0
           have i₂ := b2e170507 y X0 y
           grind)
        | exact superpose b2e170507 b2e198096
        | exact resolve b2e198096 b2e170507
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e198096
      have b2e199116 : ∀ X0 : G, (M.op x y) = (M.op (k y X0) y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
        intro X0
        first
        | (have i₁ := b2e127641 x y (k y X0)
           have i₂ := b2e198141 X0
           grind)
        | exact superpose b2e198141 b2e127641
        | (have j0 := b2e127641 x y x
           grind)
        | exact resolve b2e127641 b2e198141
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e127641 b2e198141
      have b2e199144 : ∀ X0 : G, (M.op x y) = (M.op (k y X0) y) := by
        intro X0
        first
        | (have j0 := b2e199116 X0
           grind)
        | (have r₁ := b2e199116 X0
           have r₂ := b2e241
           grind)
        | exact resolve b2e199116 b2e241
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e241 b2e199116
      have b2e199528 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (k y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e170507 y X0 X1
           have i₂ := b2e199144 X0
           grind)
        | exact superpose b2e199144 b2e170507
        | exact resolve b2e170507 b2e199144
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e170507 b2e199144
      have b2e199793 : ∀ X0 X1 : G, (M.op y X1) = (M.op (k y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e199528 X0 X1
           have i₂ := b2e16042 X1
           grind)
        | exact superpose b2e16042 b2e199528
        | exact resolve b2e199528 b2e16042
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16042 b2e199528
      have b2e200342 : ∀ X0 : G, (M.op (k (σ y) X0) (k (σ y) X0)) = (σ (M.op y (k y (τ X0)))) := by
        intro X0
        first
        | (have i₁ := b2e697 y X0
           have i₂ := b2e199793 (τ X0) (k y (τ X0))
           grind)
        | exact superpose b2e199793 b2e697
        | exact resolve b2e697 b2e199793
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e697 b2e199793
      have b2e200990 : ∀ X0 : G, (σ (M.op y y)) = (M.op (k (σ y) X0) (k (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b2e200342 X0
           have i₂ := b2e169967 y y (τ X0)
           grind)
        | exact superpose b2e169967 b2e200342
        | exact resolve b2e200342 b2e169967
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e200342
      have b2e201195 : ∀ X0 : G, (σ (M.op y y)) = (M.op (k (σ y) X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b2e200990 X0
           have i₂ := b2e169967 (k (σ y) X0) (σ y) X0
           grind)
        | exact superpose b2e169967 b2e200990
        | exact resolve b2e200990 b2e169967
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e169967 b2e200990
      have b2e201213 : ∀ X0 : G, (σ (M.op y y)) = (M.op (k (σ y) X0) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e201195 X0
           have i₂ := b2e38 (k (σ y) X0)
           grind)
        | exact superpose b2e38 b2e201195
        | exact resolve b2e201195 b2e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e201195
      have b2e201215 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ y) X0) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e201213 X0
           have i₂ := b2e15938
           grind)
        | exact superpose b2e15938 b2e201213
        | exact resolve b2e201213 b2e15938
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e15938 b2e201213
      have b2e214472 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k X0 (M.op X2 X1)) ∨ (M.op X1 X0) = (k (M.op X3 X0) X1) := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b2e5999 X0 X1 X1 X2 X3
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e5999
      have b2e296277 : ∀ X1 : G, (σ (M.op x y)) = (σ (M.op y x)) ∨ (M.op x y) = (k (M.op X1 y) x) := by
        intro X1
        first
        | (have i₁ := b2e178650 x
           have i₂ := b2e214472 y x (k x x) X1
           grind)
        | exact superpose b2e214472 b2e178650
        | (have j1 := b2e214472 y x x X1
           grind)
        | exact resolve b2e178650 b2e214472
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e178650 b2e214472
      have b2e296302 : ∀ X1 : G, (M.op x y) = (k (M.op X1 y) x) := by
        intro X1
        first
        | (have j0 := b2e296277 X1
           grind)
        | (have r₁ := b2e296277 X1
           have r₂ := b2e183
           grind)
        | exact resolve b2e296277 b2e183
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e183 b2e296277
      have b2e296647 : ∀ X0 X1 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (σ (M.op X1 y))) := by
        intro X0 X1
        first
        | (have i₁ := b2e170292 (M.op X1 y) x X0
           have i₂ := b2e296302 X1
           grind)
        | exact superpose b2e296302 b2e170292
        | exact resolve b2e170292 b2e296302
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e170292
      have b2e296718 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op X1 y))) := by
        intro X0 X1
        first
        | (have i₁ := b2e296647 X0 X1
           have i₂ := b2e16121 X0
           grind)
        | exact superpose b2e16121 b2e296647
        | exact resolve b2e296647 b2e16121
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16121 b2e296647
      have b2e298021 : ∀ X0 : G, (M.op (σ (M.op X0 y)) (σ x)) = (σ (M.op (M.op X0 y) (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b2e72 (M.op X0 y)
           have i₂ := b2e296718 (σ (M.op X0 y)) X0
           grind)
        | exact superpose b2e296718 b2e72
        | exact resolve b2e72 b2e296718
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e72 b2e296718
      have b2e298383 : ∀ X0 : G, (M.op (σ (M.op X0 y)) (σ x)) = (σ (M.op (M.op X0 y) y)) := by
        intro X0
        first
        | (have i₁ := b2e298021 X0
           have i₂ := b2e24 y (M.op X0 y) X0
           grind)
        | exact superpose b2e24 b2e298021
        | exact resolve b2e298021 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e24 b2e298021
      have b2e299808 : ∀ X0 : G, (k (τ (σ (M.op (M.op X0 y) y))) y) = (k (τ (σ (M.op (M.op X0 y) y))) x) := by
        intro X0
        first
        | (have i₁ := b2e70186 (σ (M.op X0 y))
           have i₂ := b2e298383 X0
           grind)
        | exact superpose b2e298383 b2e70186
        | exact resolve b2e70186 b2e298383
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e70186 b2e298383
      have b2e299885 : ∀ X0 : G, (k (M.op (M.op X0 y) y) y) = (k (M.op (M.op X0 y) y) x) := by
        intro X0
        first
        | (have i₁ := b2e299808 X0
           have i₂ := b2e11 (M.op (M.op X0 y) y)
           grind)
        | exact superpose b2e11 b2e299808
        | exact resolve b2e299808 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e299808
      have b2e299940 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op X0 y) y) y) := by
        intro X0
        first
        | (have i₁ := b2e299885 X0
           have i₂ := b2e296302 (M.op X0 y)
           grind)
        | exact superpose b2e296302 b2e299885
        | exact resolve b2e299885 b2e296302
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e296302 b2e299885
      have b2e299962 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 y) y) y) := by
        intro X0
        first
        | (have i₁ := b2e299940 X0
           have i₂ := b2e55698 (M.op X0 y) y
           grind)
        | exact superpose b2e55698 b2e299940
        | exact resolve b2e299940 b2e55698
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e55698 b2e299940
      have b2e299971 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) y) := by
        intro X0
        first
        | (have i₁ := b2e299962 X0
           have i₂ := b2e33 X0 y y
           grind)
        | exact superpose b2e33 b2e299962
        | exact resolve b2e299962 b2e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e33 b2e299962
      have b2e300363 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b2e89 X0 y y
           have i₂ := b2e299971 X0
           grind)
        | exact superpose b2e299971 b2e89
        | (have j0 := b2e89 X0 y x
           grind)
        | exact resolve b2e89 b2e299971
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e89 b2e299971
      have b2e300693 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have j0 := b2e300363 X0
           have j1 := b2e143358 X0
           grind)
        | (have r₁ := b2e300363 X0
           have r₂ := b2e143358 X0
           grind)
        | (have r₁ := b2e300363 x
           have r₂ := b2e143358 x
           grind)
        | exact resolve b2e300363 b2e143358
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e143358 b2e300363
      have b2e302186 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op y (σ x)) X0) := by
        intro X0
        first
        | (have i₁ := b2e185588 y X0
           have i₂ := b2e300693 (σ x)
           grind)
        | exact superpose b2e300693 b2e185588
        | exact resolve b2e185588 b2e300693
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e185588
      have b2e302212 : (σ (M.op x y)) = (M.op (M.op y (σ y)) (σ x)) := by
        first
        | (have i₁ := b2e201215 y
           have i₂ := b2e300693 (σ y)
           grind)
        | exact superpose b2e300693 b2e201215
        | exact resolve b2e201215 b2e300693
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e201215 b2e300693
      have b2e302774 : (σ (M.op x y)) = (M.op (M.op y (σ x)) (σ x)) := by
        first
        | (have i₁ := b2e302212
           have i₂ := b2e38 y
           grind)
        | exact superpose b2e38 b2e302212
        | exact resolve b2e302212 b2e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e38 b2e302212
      have b2e303073 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e302774
           have i₂ := b2e302186 (σ x)
           grind)
        | exact superpose b2e302186 b2e302774
        | exact resolve b2e302774 b2e302186
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e302186 b2e302774
      have b2e303168 : False := by grind
      exact b2e303168
    · have b3e10 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X2 X1)) := by
        intro X0 X1 X2
        grind
      have b3e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : (M.op x y) ≠ (M.op x x) := by grind
      have b3e18 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b3e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e15 X0 X0
           have i₂ := b3e53 (σ X0)
           grind)
        | exact superpose b3e53 b3e15
        | exact resolve b3e15 b3e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b3e63 X0
           have i₂ := b3e53 X0
           grind)
        | exact superpose b3e53 b3e63
        | exact resolve b3e63 b3e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e53 b3e63
      have b3e85 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 X1)) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10 X2 X0 X0
           have i₂ := b3e14 X0 X1
           grind)
        | (have i₁ := b3e10 X0 X1 X0
           have i₂ := b3e14 X0 X1
           grind)
        | exact superpose b3e14 b3e10
        | (have j1 := b3e14 X0 X1
           grind)
        | exact resolve b3e10 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e96 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e85 X0 X1 X2
           have i₂ := b3e10 X2 X1 X0
           grind)
        | exact superpose b3e10 b3e85
        | (have j0 := b3e85 X0 X1 X2
           grind)
        | exact resolve b3e85 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e85
      have b3e264 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op (σ x) X0) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e96 (σ y) X0 (σ x)
           grind)
        | (have i₁ := b3e18
           have i₂ := b3e96 X0 (σ y) (σ x)
           grind)
        | exact superpose b3e96 b3e18
        | (have j1 := b3e96 (σ y) X0 x
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e96 (σ x) (σ y) (σ x)
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e96 (σ y) (σ x) (σ x)
           grind)
        | exact resolve b3e18 b3e96
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e271 : ∀ X0 : G, (M.op (σ x) X0) ≠ (σ (M.op x x)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b3e264 X0
           have i₂ := b3e64 x
           grind)
        | exact superpose b3e64 b3e264
        | (have j0 := b3e264 X0
           grind)
        | exact resolve b3e264 b3e64
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e264
      have b3e13122 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b3e271 (σ x)
           have i₂ := b3e64 x
           grind)
        | exact superpose b3e64 b3e271
        | (have j0 := b3e271 (σ x)
           grind)
        | (have r₁ := b3e271 (σ x)
           have r₂ := b3e64 x
           grind)
        | exact resolve b3e271 b3e64
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e64 b3e271
      have b3e13133 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
      clear b3e13122
      have b3e13142 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b3e13133
           have i₂ := b3e15 y x
           grind)
        | exact superpose b3e15 b3e13133
        | exact resolve b3e13133 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e13133
      have b3e13155 : (σ (M.op x y)) ≠ (σ (k y x)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e13142
           grind)
        | exact superpose b3e13142 b3e16
        | exact resolve b3e16 b3e13142
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e13142
      have b3e13265 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 y) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b3e13155
           have i₂ := b3e96 y x X0
           grind)
        | exact superpose b3e96 b3e13155
        | (have j1 := b3e96 x y X0
           grind)
        | exact resolve b3e13155 b3e96
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e96 b3e13155
      have b3e13267 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
        intro X0
        first
        | (have j0 := b3e13265 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e13265
      have b3e13619 : (M.op x x) ≠ (M.op x x) := by
        first
        | (have i₁ := b3e17
           have i₂ := b3e13267 x
           grind)
        | exact superpose b3e13267 b3e17
        | (have r₁ := b3e17
           have r₂ := b3e13267 x
           grind)
        | exact resolve b3e17 b3e13267
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e13267
      have b3e13620 : False := by grind
      exact b3e13620

/-- `Equation3718`: `x ◇ y = (x ◇ x) ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_pyy_pxx_pyx_Equation3718 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3718 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3718.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X2 X1)) := by
        intro X0 X1 X2
        grind
      have b0e13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : (M.op y x) = (M.op y y) := by grind
      have b0e18 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e22 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 X0) (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 x y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e25 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e22 X0
           have i₂ := b0e10 X0 y y
           grind)
        | exact superpose b0e10 b0e22
        | exact resolve b0e22 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e31 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 (σ x) (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e31 X0
           have i₂ := b0e10 X0 (σ y) (σ y)
           grind)
        | exact superpose b0e10 b0e31
        | exact resolve b0e31 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e52 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e13 (σ x) (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e13
        | (have j0 := b0e13 (σ y) (σ y)
           grind)
        | (have r₁ := b0e13 (σ x) (σ y)
           have r₂ := b0e18
           grind)
        | exact resolve b0e13 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e53 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
        first
        | (have i₁ := b0e13 x y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e13
        | (have j0 := b0e13 y y
           grind)
        | (have r₁ := b0e13 x y
           have r₂ := b0e17
           grind)
        | exact resolve b0e13 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e58 : (M.op x x) = (k x y) := by grind
      clear b0e53
      have b0e59 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e52
      have b0e61 : (M.op x y) = (k x y) := by
        first
        | (have i₁ := b0e58
           have i₂ := b0e25 x
           grind)
        | exact superpose b0e25 b0e58
        | exact resolve b0e58 b0e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25 b0e58
      have b0e62 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e59
           have i₂ := b0e15 x y
           grind)
        | exact superpose b0e15 b0e59
        | exact resolve b0e59 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59
      have b0e66 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e62
           have i₂ := b0e61
           grind)
        | exact superpose b0e61 b0e62
        | exact resolve b0e62 b0e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61 b0e62
      have b0e68 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e66
           have i₂ := b0e32 (σ x)
           grind)
        | exact superpose b0e32 b0e66
        | exact resolve b0e66 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e66
      have b0e69 : False := by grind
      exact b0e69
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X2 X1)) := by
        intro X0 X1 X2
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b1e17 : (M.op y x) = (M.op y y) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b1e20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e15
        | exact resolve b1e15 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e21 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 X1)) = (M.op (M.op X0 X0) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (M.op X0 X0) X1 X2
           have i₂ := b1e10 X0 X0 X0
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e22 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 X0) (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b1e10 X0 x y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X2 (M.op X3 X1) (M.op X0 X0)
           have i₂ := b1e10 X0 X1 X3
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e24 : ∀ X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op X3 X1)) := by
        intro X1 X2 X3
        first
        | (have i₁ := b1e23 x X1 X2 X3
           have i₂ := b1e10 X2 X1 x
           grind)
        | exact superpose b1e10 b1e23
        | exact resolve b1e23 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23
      have b1e25 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b1e22 X0
           have i₂ := b1e10 X0 y y
           grind)
        | exact superpose b1e10 b1e22
        | exact resolve b1e22 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22
      have b1e26 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e21 X0 X1 x
           have i₂ := b1e10 X0 X1 x
           grind)
        | exact superpose b1e10 b1e21
        | exact resolve b1e21 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21
      have b1e45 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
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
      have b1e47 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 y) ∨ (M.op x x) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e13 x X0
           have i₂ := b1e25 X0
           grind)
        | exact superpose b1e25 b1e13
        | (have j0 := b1e13 y X0
           grind)
        | (have r₁ := b1e13 x y
           have r₂ := b1e25 y
           grind)
        | (have r₁ := b1e13 y x
           have r₂ := b1e25 x
           grind)
        | exact resolve b1e13 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e48 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op X2 X1) (M.op X2 X1)) = (k (M.op X2 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e13 (M.op X2 X1) X0
           have i₂ := b1e24 X1 X0 X2
           grind)
        | exact superpose b1e24 b1e13
        | (have j0 := b1e13 X1 X0
           grind)
        | (have r₁ := b1e13 X1 (M.op x X1)
           have r₂ := b1e24 X1 (M.op x X1) x
           grind)
        | (have r₁ := b1e13 (M.op x X1) X1
           have r₂ := b1e24 X1 X1 x
           grind)
        | exact resolve b1e13 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 X1 (M.op X0 X0)
           have i₂ := b1e10 X0 X0 X0
           grind)
        | exact superpose b1e10 b1e13
        | (have j0 := b1e13 X1 (M.op X0 X0)
           grind)
        | exact resolve b1e13 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e51 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X2 X2) = (k X2 (M.op X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e13 X2 (M.op X0 X1)
           have i₂ := b1e24 X1 (M.op X0 X1) X0
           grind)
        | exact superpose b1e24 b1e13
        | (have j0 := b1e13 X2 (M.op X0 X1)
           grind)
        | (have r₁ := b1e13 X1 (M.op x X1)
           have r₂ := b1e24 X1 (M.op x X1) x
           grind)
        | (have r₁ := b1e13 (M.op x X1) X1
           have r₂ := b1e24 X1 X1 x
           grind)
        | exact resolve b1e13 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b1e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e53 : (M.op x x) = (k x y) := by grind
      clear b1e45
      have b1e54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e49 X0 X1
           have i₂ := b1e26 X0 X1
           grind)
        | exact superpose b1e26 b1e49
        | (have j0 := b1e49 X0 X1
           grind)
        | (have r₁ := b1e49 X1 X1
           have r₂ := b1e26 X1 X1
           grind)
        | exact resolve b1e49 b1e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e49
      have b1e55 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op X2 X1) X0) = (M.op (M.op X2 X1) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e48 X0 X1 X2
           have i₂ := b1e24 X1 (M.op X2 X1) X2
           grind)
        | exact superpose b1e24 b1e48
        | (have j0 := b1e48 X0 X1 X2
           grind)
        | (have r₁ := b1e48 (M.op x X1) X1 X2
           have r₂ := b1e24 X1 (M.op x X1) x
           grind)
        | (have r₁ := b1e48 X1 (M.op x X1) X2
           have r₂ := b1e24 X1 X1 x
           grind)
        | exact resolve b1e48 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e48
      have b1e56 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 y) ∨ (M.op x y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e47 X0
           have i₂ := b1e25 x
           grind)
        | exact superpose b1e25 b1e47
        | (have j0 := b1e47 X0
           grind)
        | (have r₁ := b1e47 x
           have r₂ := b1e25 x
           grind)
        | exact resolve b1e47 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e47
      have b1e58 : (M.op x y) = (k x y) := by
        first
        | (have i₁ := b1e53
           have i₂ := b1e25 x
           grind)
        | exact superpose b1e25 b1e53
        | exact resolve b1e53 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53
      have b1e61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e15 X0 X0
           have i₂ := b1e52 (σ X0)
           grind)
        | exact superpose b1e52 b1e15
        | exact resolve b1e15 b1e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e62 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b1e61 X0
           have i₂ := b1e52 X0
           grind)
        | exact superpose b1e52 b1e61
        | exact resolve b1e61 b1e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e61
      have b1e65 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X2 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e14 (M.op x X1) X2
           have i₂ := b1e24 X1 X2 x
           grind)
        | exact superpose b1e24 b1e14
        | (have j0 := b1e14 X1 X0
           grind)
        | exact resolve b1e14 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e66 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e14 x X0
           have i₂ := b1e25 X0
           grind)
        | exact superpose b1e25 b1e14
        | (have j0 := b1e14 y X0
           grind)
        | exact resolve b1e14 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e71 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 X1 X0
           have i₂ := b1e14 X1 X0
           grind)
        | (have i₁ := b1e13 X1 X1
           have i₂ := b1e14 X0 X1
           grind)
        | exact superpose b1e14 b1e13
        | (have j0 := b1e13 X0 X0
           have j1 := b1e14 X1 X0
           grind)
        | (have r₁ := b1e13 X0 X1
           have r₂ := b1e14 X0 X1
           grind)
        | (have r₁ := b1e13 X0 X0
           have r₂ := b1e14 X0 X0
           grind)
        | exact resolve b1e13 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e81 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 X1)) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 X2 X0 X0
           have i₂ := b1e14 X1 X0
           grind)
        | (have i₁ := b1e10 X0 X0 X1
           have i₂ := b1e14 X0 X1
           grind)
        | exact superpose b1e14 b1e10
        | (have j1 := b1e14 X1 X0
           grind)
        | exact resolve b1e10 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e84 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X1 X0
           have i₂ := b1e14 (σ X1) (σ X0)
           grind)
        | exact superpose b1e14 b1e15
        | (have j1 := b1e14 (σ X1) (σ X0)
           grind)
        | exact resolve b1e15 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e86 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b1e71 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e71
      have b1e87 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e84 X0 X1
           have i₂ := b1e62 X0
           grind)
        | exact superpose b1e62 b1e84
        | (have j0 := b1e84 X0 X1
           grind)
        | exact resolve b1e84 b1e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e84
      have b1e89 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e81 X0 X1 X2
           have i₂ := b1e10 X2 X1 X0
           grind)
        | exact superpose b1e10 b1e81
        | (have j0 := b1e81 X0 X1 X2
           grind)
        | exact resolve b1e81 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e81
      have b1e175 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b1e19 X0 (τ X0)
           have i₂ := b1e52 (τ X0)
           grind)
        | exact superpose b1e52 b1e19
        | exact resolve b1e19 b1e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e179 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k (τ X0) X1)
           have i₂ := b1e19 X0 X1
           grind)
        | exact superpose b1e19 b1e11
        | exact resolve b1e11 b1e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19
      have b1e180 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b1e175 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e175
        | exact resolve b1e175 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e175
      have b1e181 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b1e180 X0
           have i₂ := b1e52 X0
           grind)
        | exact superpose b1e52 b1e180
        | exact resolve b1e180 b1e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e52 b1e180
      have b1e189 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k X0 (τ X1))
           have i₂ := b1e20 X1 X0
           grind)
        | exact superpose b1e20 b1e11
        | exact resolve b1e11 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20
      have b1e223 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b1e86 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e254 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e26 (σ X0) X1
           have i₂ := b1e62 X0
           grind)
        | exact superpose b1e62 b1e26
        | exact resolve b1e26 b1e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e26
      have b1e290 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X2) ∨ (M.op X2 X0) = (k X0 X2) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e86 X2 X0
           have i₂ := b1e89 X1 X0 X0
           grind)
        | (have i₁ := b1e86 X0 X0
           have i₂ := b1e89 X0 X1 X0
           grind)
        | exact superpose b1e89 b1e86
        | (have j0 := b1e86 X2 X0
           have j1 := b1e89 X2 X0 X2
           grind)
        | exact resolve b1e86 b1e89
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e293 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X2 X2) = (k X2 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e13 X2 X0
           have i₂ := b1e89 X1 X0 X0
           grind)
        | (have i₁ := b1e13 X0 X0
           have i₂ := b1e89 X0 X1 X0
           grind)
        | exact superpose b1e89 b1e13
        | (have j0 := b1e13 X2 X0
           have j1 := b1e89 X1 X0 X2
           grind)
        | (have r₁ := b1e13 X1 X0
           have r₂ := b1e89 X0 X1 X0
           grind)
        | (have r₁ := b1e13 X0 X1
           have r₂ := b1e89 X0 X1 X1
           grind)
        | exact resolve b1e13 b1e89
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e296 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X2 X2) = (k X2 X0) ∨ (M.op X1 X2) = (k X2 X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e13 X2 X0
           have i₂ := b1e89 X1 X2 X0
           grind)
        | (have i₁ := b1e13 X0 X2
           have i₂ := b1e89 X0 X1 X2
           grind)
        | exact superpose b1e89 b1e13
        | (have j0 := b1e13 X1 X0
           have j1 := b1e89 X1 X2 X2
           grind)
        | (have r₁ := b1e13 X1 X0
           have r₂ := b1e89 X0 X1 X0
           grind)
        | (have r₁ := b1e13 X0 X1
           have r₂ := b1e89 X0 X1 X1
           grind)
        | exact resolve b1e13 b1e89
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e321 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e16
           have i₂ := b1e89 (σ y) X0 (σ x)
           grind)
        | (have i₁ := b1e16
           have i₂ := b1e89 X0 (σ y) (σ x)
           grind)
        | exact superpose b1e89 b1e16
        | (have j1 := b1e89 (σ y) X0 x
           grind)
        | exact resolve b1e16 b1e89
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e354 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e179 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e179
        | exact resolve b1e179 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e371 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (k X0 (k X0 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e54 X1 X1
           have i₂ := b1e86 X0 X1
           grind)
        | exact superpose b1e86 b1e54
        | (have j1 := b1e86 X1 X0
           grind)
        | exact resolve b1e54 b1e86
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e393 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
        intro X0
        first
        | (have j0 := b1e54 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54
      have b1e398 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X0 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b1e371 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e371
      have b1e754 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) (σ X1)) (σ X2)) = (σ (k X2 (M.op X0 X0))) ∨ (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (σ X0) (σ X1)) (σ X2)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e87 (M.op X0 X0) X1
           have i₂ := b1e87 X0 X1
           grind)
        | exact superpose b1e87 b1e87
        | (have j0 := b1e87 X0 X1
           have j1 := b1e87 X0 X1
           grind)
        | exact resolve b1e87 b1e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e782 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e87 x y
           grind)
        | exact superpose b1e87 b1e16
        | (have j1 := b1e87 x y
           grind)
        | exact resolve b1e16 b1e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e798 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e24 (σ X0) X2 (σ X1)
           have i₂ := b1e87 X1 X0
           grind)
        | exact superpose b1e87 b1e24
        | (have j1 := b1e87 X1 X0
           grind)
        | exact resolve b1e24 b1e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e805 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e87 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e812 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
        first
        | (have i₁ := b1e782
           have i₂ := b1e25 x
           grind)
        | exact superpose b1e25 b1e782
        | exact resolve b1e782 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e782
      have b1e823 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) (σ X1)) (σ X2)) = (σ (k X2 (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (M.op (σ X0) (σ X1)) (σ X2)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e754 X0 X1 X2
           have i₂ := b1e10 X0 X0 X0
           grind)
        | exact superpose b1e10 b1e754
        | (have j0 := b1e754 X0 X1 X2
           grind)
        | exact resolve b1e754 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e754
      have b1e843 : (σ (M.op x y)) ≠ (σ (k y x)) := by
        first
        | (have r₁ := b1e812
           have r₂ := b1e16
           grind)
        | exact resolve b1e812 b1e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e812
      have b1e882 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b1e843
           have i₂ := b1e86 x y
           grind)
        | exact superpose b1e86 b1e843
        | (have j1 := b1e86 x y
           grind)
        | exact resolve b1e843 b1e86
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e86
      have b1e885 : (M.op y y) = (k y x) := by grind
      clear b1e882
      have b1e1100 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b1e843
           have i₂ := b1e885
           grind)
        | exact superpose b1e885 b1e843
        | exact resolve b1e843 b1e885
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e843
      have b1e1515 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) X0) := by
        intro X0
        first
        | (have i₁ := b1e254 x X0
           have i₂ := b1e25 x
           grind)
        | exact superpose b1e25 b1e254
        | exact resolve b1e254 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1970 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op x y) = (k x X0) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e56 X0
           have i₂ := b1e66 X0
           grind)
        | (have i₁ := b1e56 y
           have i₂ := b1e66 y
           grind)
        | exact superpose b1e66 b1e56
        | (have j0 := b1e56 X0
           have j1 := b1e66 X0
           grind)
        | (have r₁ := b1e56 X0
           have r₂ := b1e66 X0
           grind)
        | (have r₁ := b1e56 y
           have r₂ := b1e66 y
           grind)
        | exact resolve b1e56 b1e66
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e56
      have b1e1995 : ∀ X0 : G, (M.op x y) = (k x X0) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have j0 := b1e1970 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1970
      have b1e2254 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X0 X0)) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e223 (M.op X0 X0) X1
           have i₂ := b1e10 X0 X0 X0
           grind)
        | exact superpose b1e10 b1e223
        | (have j0 := b1e223 (M.op X0 X0) X1
           grind)
        | exact resolve b1e223 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e2274 : ∀ X0 : G, (M.op X0 y) ≠ (M.op x x) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e223 x X0
           have i₂ := b1e25 X0
           grind)
        | exact superpose b1e25 b1e223
        | exact resolve b1e223 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e223
      have b1e2297 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e2274 X0
           have i₂ := b1e25 x
           grind)
        | exact superpose b1e25 b1e2274
        | (have j0 := b1e2274 X0
           grind)
        | (have r₁ := b1e2274 x
           have r₂ := b1e25 x
           grind)
        | exact resolve b1e2274 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2274
      have b1e2309 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e2254 X0 X1
           have i₂ := b1e24 X0 X1 X0
           grind)
        | exact superpose b1e24 b1e2254
        | (have j0 := b1e2254 X0 X1
           grind)
        | (have r₁ := b1e2254 x x
           have r₂ := b1e24 x x x
           grind)
        | exact resolve b1e2254 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2254
      have b1e2321 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e2309 X0 X1
           have i₂ := b1e24 X0 X1 X0
           grind)
        | exact superpose b1e24 b1e2309
        | (have j0 := b1e2309 X0 X1
           grind)
        | exact resolve b1e2309 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2309
      have b1e10361 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) := by
        intro X0 X1
        first
        | (have j0 := b1e55 X1 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e55
      have b1e10528 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X1 X2) = (k X2 X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10361 X2 X1
           have i₂ := b1e89 X0 X1 X2
           grind)
        | (have i₁ := b1e10361 X2 X0
           have i₂ := b1e89 X0 X1 X2
           grind)
        | exact superpose b1e89 b1e10361
        | (have j1 := b1e89 X1 X2 X2
           grind)
        | exact resolve b1e10361 b1e89
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e89
      have b1e10544 : ∀ X0 : G, (M.op (M.op X0 y) x) = (k (M.op X0 y) x) := by
        intro X0
        first
        | (have i₁ := b1e10361 X0 x
           have i₂ := b1e25 X0
           grind)
        | exact superpose b1e25 b1e10361
        | exact resolve b1e10361 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e10361
      have b1e10606 : ∀ X0 : G, (M.op (M.op X0 y) y) = (k (M.op X0 y) x) := by
        intro X0
        first
        | (have i₁ := b1e10544 X0
           have i₂ := b1e25 (M.op X0 y)
           grind)
        | exact superpose b1e25 b1e10544
        | exact resolve b1e10544 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e10544
      have b1e13690 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b1e321 (σ x)
           have i₂ := b1e62 x
           grind)
        | exact superpose b1e62 b1e321
        | (have j0 := b1e321 (σ x)
           grind)
        | exact resolve b1e321 b1e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e13702 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (k (M.op X1 X0) (σ y)) = (M.op (σ y) (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e321 (M.op X1 X0)
           have i₂ := b1e24 X0 (σ x) X1
           grind)
        | exact superpose b1e24 b1e321
        | (have j0 := b1e321 X0
           grind)
        | exact resolve b1e321 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e321
      have b1e13720 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ y) X0) = (k (M.op X1 X0) (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13702 X0 X1
           have i₂ := b1e24 X0 (σ y) X1
           grind)
        | exact superpose b1e24 b1e13702
        | (have j0 := b1e13702 X0 X1
           grind)
        | exact resolve b1e13702 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13702
      have b1e13723 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b1e13690
           have i₂ := b1e25 x
           grind)
        | exact superpose b1e25 b1e13690
        | exact resolve b1e13690 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13690
      have b1e13724 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b1e13723
      have b1e13732 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e13724
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e13724
        | exact resolve b1e13724 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13724
      have b1e13734 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e13732
           have i₂ := b1e58
           grind)
        | exact superpose b1e58 b1e13732
        | exact resolve b1e13732 b1e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e58 b1e13732
      have b1e19591 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e805 (τ X0) (τ X1)
           have i₂ := b1e354 X0 X1
           grind)
        | exact superpose b1e354 b1e805
        | exact resolve b1e805 b1e354
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e19617 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e19591 X0 X1
           have i₂ := b1e181 X1
           grind)
        | exact superpose b1e181 b1e19591
        | (have j0 := b1e19591 X0 X1
           grind)
        | exact resolve b1e19591 b1e181
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19591
      have b1e19673 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e19617 X0 X1
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e19617
        | (have j0 := b1e19617 X0 X1
           grind)
        | exact resolve b1e19617 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19617
      have b1e19711 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e19673 X0 X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e19673
        | (have j0 := b1e19673 X0 X1
           grind)
        | exact resolve b1e19673 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19673
      have b1e19738 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e19711 X0 X1
           have i₂ := b1e12 X1
           grind)
        | exact superpose b1e12 b1e19711
        | (have j0 := b1e19711 X0 X1
           grind)
        | exact resolve b1e19711 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19711
      have b1e19758 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e19738 X0 X1
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e19738
        | (have j0 := b1e19738 X0 X1
           grind)
        | exact resolve b1e19738 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19738
      have b1e19877 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x y) ∨ (M.op x y) = (M.op X0 x) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e19758 x X0
           have i₂ := b1e1995 X0
           grind)
        | exact superpose b1e1995 b1e19758
        | (have j1 := b1e1995 X0
           grind)
        | (have r₁ := b1e19758 x y
           have r₂ := b1e1995 y
           grind)
        | exact resolve b1e19758 b1e1995
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e19883 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (M.op X0 X0) ≠ (M.op x y) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e19877 X0
           have i₂ := b1e25 X0
           grind)
        | exact superpose b1e25 b1e19877
        | (have j0 := b1e19877 X0
           grind)
        | (have r₁ := b1e19877 x
           have r₂ := b1e25 x
           grind)
        | exact resolve b1e19877 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19877
      have b1e19933 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x y) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have j0 := b1e19883 X0
           have j1 := b1e2297 X0
           grind)
        | (have r₁ := b1e19883 X0
           have r₂ := b1e2297 X0
           grind)
        | (have r₁ := b1e19883 x
           have r₂ := b1e2297 x
           grind)
        | exact resolve b1e19883 b1e2297
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19883
      have b1e21385 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e51 X1 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e51
      have b1e21601 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op X1 (σ X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b1e189 X0 (M.op X1 (σ X0))
           have i₂ := b1e21385 (σ X0) X1
           grind)
        | exact superpose b1e21385 b1e189
        | exact resolve b1e189 b1e21385
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e189 b1e21385
      have b1e21615 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k X0 (τ (M.op X1 (σ X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b1e21601 X0 X1
           have i₂ := b1e62 X0
           grind)
        | exact superpose b1e62 b1e21601
        | exact resolve b1e21601 b1e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21601
      have b1e21656 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (M.op X1 (σ X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b1e21615 X0 X1
           have i₂ := b1e11 (M.op X0 X0)
           grind)
        | exact superpose b1e11 b1e21615
        | exact resolve b1e21615 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21615
      have b1e43996 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b1e290 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e44000 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b1e290 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e290
      have b1e44001 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b1e44000 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e44000
      have b1e44003 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b1e43996 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e43996
      have b1e44817 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e19758 X0 X1
           have i₂ := b1e44001 X0 X1
           grind)
        | exact superpose b1e44001 b1e19758
        | (have j0 := b1e19758 X0 X1
           have j1 := b1e44001 X0 X1
           grind)
        | (have r₁ := b1e19758 X1 X1
           have r₂ := b1e44001 X1 X1
           grind)
        | (have r₁ := b1e19758 X0 X0
           have r₂ := b1e44001 X0 X0
           grind)
        | exact resolve b1e19758 b1e44001
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19758
      have b1e44970 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b1e44001 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e45042 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b1e44817 X0 X1
           have j1 := b1e44003 X0 X1
           grind)
        | (have r₁ := b1e44817 X0 X1
           have r₂ := b1e44003 X0 X1
           grind)
        | (have r₁ := b1e44817 X1 X0
           have r₂ := b1e44003 X0 X1
           grind)
        | exact resolve b1e44817 b1e44003
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e44817
      have b1e46567 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X1) X0) ∨ (M.op (M.op X2 X1) X0) = (k X0 (M.op X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e44003 X0 (M.op X2 X1)
           have i₂ := b1e24 X1 X0 X2
           grind)
        | exact superpose b1e24 b1e44003
        | (have j0 := b1e44003 X0 (M.op X2 X1)
           grind)
        | exact resolve b1e44003 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e46678 : ∀ X0 : G, (M.op X0 y) ≠ (M.op x X0) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e44003 x X0
           have i₂ := b1e25 X0
           grind)
        | exact superpose b1e25 b1e44003
        | exact resolve b1e44003 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e46704 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e44003 (σ X1) (σ X0)
           have i₂ := b1e87 X0 X1
           grind)
        | exact superpose b1e87 b1e44003
        | (have j1 := b1e87 X0 X1
           grind)
        | exact resolve b1e44003 b1e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e87
      have b1e46759 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e46704 X0 X1
           have i₂ := b1e15 X1 X0
           grind)
        | exact superpose b1e15 b1e46704
        | (have j0 := b1e46704 X0 X1
           grind)
        | exact resolve b1e46704 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e46704
      have b1e46855 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e46759 X0 X1
           have j1 := b1e805 X0 X1
           grind)
        | (have r₁ := b1e46759 X0 X1
           have r₂ := b1e805 X0 X1
           grind)
        | exact resolve b1e46759 b1e805
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e805 b1e46759
      have b1e47088 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b1e293 X1 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e293
      have b1e47390 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e47088 X1 X0
           have i₂ := b1e44001 X1 X0
           grind)
        | exact superpose b1e44001 b1e47088
        | (have j0 := b1e47088 X1 X0
           have j1 := b1e44001 X1 X0
           grind)
        | exact resolve b1e47088 b1e44001
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e44001
      have b1e47490 : ∀ X0 : G, (M.op x y) = (M.op X0 x) ∨ (M.op X0 X0) = (k X0 x) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e47088 X0 x
           have i₂ := b1e1995 X0
           grind)
        | exact superpose b1e1995 b1e47088
        | (have j0 := b1e47088 X0 x
           have j1 := b1e1995 X0
           grind)
        | exact resolve b1e47088 b1e1995
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1995
      have b1e48007 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 x) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e47490 X0
           have i₂ := b1e25 X0
           grind)
        | exact superpose b1e25 b1e47490
        | (have j0 := b1e47490 X0
           grind)
        | exact resolve b1e47490 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e47490
      have b1e48056 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b1e47390 X0 X1
           have j1 := b1e45042 X0 X1
           grind)
        | (have r₁ := b1e47390 X0 X1
           have r₂ := b1e45042 X0 X1
           grind)
        | (have r₁ := b1e47390 X0 X0
           have r₂ := b1e45042 X0 X0
           grind)
        | exact resolve b1e47390 b1e45042
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e47390
      have b1e48177 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have j0 := b1e48007 X0
           have j1 := b1e2297 X0
           grind)
        | (have r₁ := b1e48007 X0
           have r₂ := b1e2297 X0
           grind)
        | (have r₁ := b1e48007 x
           have r₂ := b1e2297 x
           grind)
        | exact resolve b1e48007 b1e2297
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2297 b1e48007
      have b1e50683 : ∀ X0 : G, (M.op X0 y) ≠ (M.op x X0) ∨ (M.op x X0) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e44970 x X0
           have i₂ := b1e25 X0
           grind)
        | exact superpose b1e25 b1e44970
        | (have j0 := b1e44970 x X0
           grind)
        | exact resolve b1e44970 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e44970
      have b1e50998 : ∀ X0 : G, (M.op y y) ≠ (M.op y y) ∨ (M.op X0 X0) = (k X0 y) ∨ (M.op x X0) = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b1e296 y x X0
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e296
        | (have j0 := b1e296 y y X0
           grind)
        | (have r₁ := b1e296 y x x
           have r₂ := b1e17
           grind)
        | exact resolve b1e296 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e296
      have b1e51081 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ (M.op x X0) = (k X0 x) := by
        intro X0
        first
        | (have j0 := b1e50998 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e50998
      have b1e51660 : ∀ X0 : G, (M.op X0 X0) = (M.op x X0) ∨ (M.op X0 x) = (k x X0) ∨ (M.op X0 X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b1e47088 X0 x
           have i₂ := b1e51081 X0
           grind)
        | exact superpose b1e51081 b1e47088
        | (have j0 := b1e47088 X0 y
           have j1 := b1e51081 X0
           grind)
        | exact resolve b1e47088 b1e51081
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e47088 b1e51081
      have b1e51688 : ∀ X0 : G, (M.op X0 x) = (k x X0) ∨ (M.op X0 X0) = (k X0 y) := by
        intro X0
        first
        | (have j0 := b1e51660 X0
           have j1 := b1e45042 x X0
           grind)
        | (have r₁ := b1e51660 x
           have r₂ := b1e45042 x x
           grind)
        | (have r₁ := b1e51660 x
           have r₂ := b1e45042 x x
           grind)
        | exact resolve b1e51660 b1e45042
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e45042 b1e51660
      have b1e51814 : ∀ X0 : G, (M.op X0 y) = (k x X0) ∨ (M.op X0 X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b1e51688 X0
           have i₂ := b1e25 X0
           grind)
        | exact superpose b1e25 b1e51688
        | (have j0 := b1e51688 X0
           grind)
        | exact resolve b1e51688 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e51688
      have b1e54911 : ∀ X0 X1 X2 : G, (M.op X2 (σ (τ X0))) = (M.op X2 (σ (τ (k X0 X1)))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e798 (τ X0) (τ X1) X2
           have i₂ := b1e354 X1 X0
           grind)
        | exact superpose b1e354 b1e798
        | (have j0 := b1e798 (τ X0) (τ X1) X2
           grind)
        | exact resolve b1e798 b1e354
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e354 b1e798
      have b1e55755 : ∀ X0 X1 X2 : G, (M.op X2 (k X0 X1)) = (M.op X2 (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e54911 X0 X1 X2
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e54911
        | (have j0 := b1e54911 X0 X1 X2
           grind)
        | exact resolve b1e54911 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54911
      have b1e55862 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (k X0 X1)) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e55755 X0 X1 X2
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e55755
        | (have j0 := b1e55755 X0 X1 X2
           grind)
        | exact resolve b1e55755 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e55755
      have b1e55915 : ∀ X0 X1 X2 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e55862 X0 X1 X2
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e55862
        | (have j0 := b1e55862 X0 X1 X2
           grind)
        | exact resolve b1e55862 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e55862
      have b1e55946 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e55915 X0 X1 X2
           have i₂ := b1e12 X1
           grind)
        | exact superpose b1e12 b1e55915
        | (have j0 := b1e55915 X0 X1 X2
           grind)
        | exact resolve b1e55915 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e55915
      have b1e55963 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e55946 X0 X1 X2
           have i₂ := b1e181 X1
           grind)
        | exact superpose b1e181 b1e55946
        | (have j0 := b1e55946 X0 X1 X2
           grind)
        | exact resolve b1e55946 b1e181
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e181 b1e55946
      have b1e58174 : ∀ X0 : G, (M.op X0 X0) = (M.op x X0) ∨ (M.op x X0) = (k x X0) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e48056 X0 x
           have i₂ := b1e48177 X0
           grind)
        | exact superpose b1e48177 b1e48056
        | (have j0 := b1e48056 X0 x
           have j1 := b1e48177 X0
           grind)
        | exact resolve b1e48056 b1e48177
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e48177
      have b1e60071 : ∀ X0 : G, (M.op x y) ≠ (k X0 y) ∨ (M.op X0 y) = (k x X0) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e19933 X0
           have i₂ := b1e51814 X0
           grind)
        | exact superpose b1e51814 b1e19933
        | (have j0 := b1e19933 X0
           have j1 := b1e51814 X0
           grind)
        | exact resolve b1e19933 b1e51814
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19933 b1e51814
      have b1e60282 : ∀ X0 : G, (M.op x y) ≠ (k X0 y) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have j0 := b1e60071 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e60071
      have b1e62777 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x X0) ∨ (M.op x X0) = (k x X0) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e50683 X0
           have i₂ := b1e66 X0
           grind)
        | (have i₁ := b1e50683 y
           have i₂ := b1e66 y
           grind)
        | exact superpose b1e66 b1e50683
        | (have j0 := b1e50683 X0
           have j1 := b1e66 X0
           grind)
        | (have r₁ := b1e50683 x
           have r₂ := b1e66 x
           grind)
        | exact resolve b1e50683 b1e66
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e66 b1e50683
      have b1e62852 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have j0 := b1e62777 X0
           have j1 := b1e58174 X0
           grind)
        | (have r₁ := b1e62777 X0
           have r₂ := b1e58174 X0
           grind)
        | (have r₁ := b1e62777 x
           have r₂ := b1e58174 x
           grind)
        | exact resolve b1e62777 b1e58174
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e58174 b1e62777
      have b1e73840 : ∀ X0 : G, (M.op x X0) = (k x (M.op x X0)) ∨ (M.op X0 x) = (M.op x X0) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e398 x X0
           have i₂ := b1e62852 X0
           grind)
        | exact superpose b1e62852 b1e398
        | (have j1 := b1e62852 X0
           grind)
        | exact resolve b1e398 b1e62852
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e398 b1e62852
      have b1e73982 : ∀ X0 : G, (M.op X0 y) = (M.op x X0) ∨ (M.op x X0) = (k x (M.op x X0)) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e73840 X0
           have i₂ := b1e25 X0
           grind)
        | exact superpose b1e25 b1e73840
        | (have j0 := b1e73840 X0
           grind)
        | exact resolve b1e73840 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e73840
      have b1e74053 : ∀ X0 : G, (M.op x X0) = (k x (M.op x X0)) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have j0 := b1e73982 X0
           have j1 := b1e46678 X0
           grind)
        | (have r₁ := b1e73982 X0
           have r₂ := b1e46678 X0
           grind)
        | exact resolve b1e73982 b1e46678
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e73982
      have b1e94394 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k (M.op X2 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e2321 X1 X0
           have i₂ := b1e65 X0 X1 X2
           grind)
        | (have i₁ := b1e2321 X0 X0
           have i₂ := b1e65 X0 X1 X2
           grind)
        | exact superpose b1e65 b1e2321
        | (have j1 := b1e65 X0 X1 X0
           grind)
        | (have r₁ := b1e2321 X1 X1
           have r₂ := b1e65 X1 X1 X2
           grind)
        | exact resolve b1e2321 b1e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e65 b1e2321
      have b1e94441 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k (M.op X2 X1) X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b1e94394 X0 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e94394
      have b1e133220 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ X0) (σ X1)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (M.op (σ X0) (σ X1)) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e823 X0 X1 X0
           have i₂ := b1e393 X0
           grind)
        | exact superpose b1e393 b1e823
        | (have j0 := b1e823 X0 X1 X0
           grind)
        | exact resolve b1e823 b1e393
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e393 b1e823
      have b1e133691 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ X0) (σ X1)) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e133220 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e133220
      have b1e138918 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X1) = (M.op X2 (k X1 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e13 X1 X0
           have i₂ := b1e55963 X1 X0 X2
           grind)
        | (have i₁ := b1e13 X1 X1
           have i₂ := b1e55963 X0 X1 X2
           grind)
        | exact superpose b1e55963 b1e13
        | (have j0 := b1e13 X0 X0
           have j1 := b1e55963 X1 X0 X2
           grind)
        | (have r₁ := b1e13 X0 X1
           have r₂ := b1e55963 X0 X1 X2
           grind)
        | (have r₁ := b1e13 X0 X0
           have r₂ := b1e55963 X0 X0 X2
           grind)
        | (have r₁ := b1e13 X0 (k X0 X1)
           have r₂ := b1e55963 X0 X1 (k X0 X1)
           grind)
        | exact resolve b1e13 b1e55963
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e55963
      have b1e139068 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X1) = (M.op X2 (k X1 X0)) := by
        intro X0 X1 X2
        first
        | (have j0 := b1e138918 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e138918
      have b1e145489 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X2 (k X0 X1)) ∨ (M.op X3 X0) = (M.op X3 (k X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e24 X0 X2 X0
           have i₂ := b1e139068 X1 X0 X3
           grind)
        | exact superpose b1e139068 b1e24
        | (have j1 := b1e139068 X1 X0 X2
           grind)
        | exact resolve b1e24 b1e139068
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e139068
      have b1e151500 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (k (M.op X0 (σ x)) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e13720 (σ x) X0
           have i₂ := b1e62 x
           grind)
        | exact superpose b1e62 b1e13720
        | (have j0 := b1e13720 (σ x) X0
           grind)
        | exact resolve b1e13720 b1e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e62 b1e13720
      have b1e151501 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (k (M.op X0 (σ x)) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e151500 X0
           have i₂ := b1e25 x
           grind)
        | exact superpose b1e25 b1e151500
        | (have j0 := b1e151500 X0
           grind)
        | exact resolve b1e151500 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e151500
      have b1e151502 : ∀ X0 : G, (M.op (σ y) (σ x)) = (k (M.op X0 (σ x)) (σ y)) := by
        intro X0
        first
        | (have j0 := b1e151501 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e151501
      have b1e151503 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op X0 (σ x)) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e151502 X0
           have i₂ := b1e13734
           grind)
        | exact superpose b1e13734 b1e151502
        | exact resolve b1e151502 b1e13734
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13734 b1e151502
      have b1e151644 : ∀ X0 : G, (τ (σ (M.op x y))) = (k (τ (M.op X0 (σ x))) y) := by
        intro X0
        first
        | (have i₁ := b1e179 (M.op X0 (σ x)) y
           have i₂ := b1e151503 X0
           grind)
        | exact superpose b1e151503 b1e179
        | exact resolve b1e179 b1e151503
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e151503
      have b1e151653 : ∀ X0 : G, (M.op x y) = (k (τ (M.op X0 (σ x))) y) := by
        intro X0
        first
        | (have i₁ := b1e151644 X0
           have i₂ := b1e11 (M.op x y)
           grind)
        | exact superpose b1e11 b1e151644
        | exact resolve b1e151644 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e151644
      have b1e151856 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op (τ (M.op X0 (σ x))) y) = (k x (τ (M.op X0 (σ x)))) := by
        intro X0
        first
        | (have i₁ := b1e60282 (τ (M.op X0 (σ x)))
           have i₂ := b1e151653 X0
           grind)
        | exact superpose b1e151653 b1e60282
        | (have j0 := b1e60282 (τ (M.op X0 (σ x)))
           grind)
        | (have r₁ := b1e60282 (τ (M.op X0 (σ x)))
           have r₂ := b1e151653 X0
           grind)
        | exact resolve b1e60282 b1e151653
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e60282
      have b1e151866 : ∀ X0 : G, (M.op (τ (M.op X0 (σ x))) y) = (k x (τ (M.op X0 (σ x)))) := by
        intro X0
        first
        | (have j0 := b1e151856 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e151856
      have b1e151870 : ∀ X0 : G, (M.op x x) = (M.op (τ (M.op X0 (σ x))) y) := by
        intro X0
        first
        | (have i₁ := b1e151866 X0
           have i₂ := b1e21656 x X0
           grind)
        | exact superpose b1e21656 b1e151866
        | exact resolve b1e151866 b1e21656
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21656 b1e151866
      have b1e151913 : ∀ X0 : G, (M.op x y) = (M.op (τ (M.op X0 (σ x))) y) := by
        intro X0
        first
        | (have i₁ := b1e151870 X0
           have i₂ := b1e25 x
           grind)
        | exact superpose b1e25 b1e151870
        | exact resolve b1e151870 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e151870
      have b1e164858 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
        intro X0 X1
        first
        | (have j0 := b1e94441 X0 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e94441
      have b1e164859 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
        intro X0 X1
        first
        | (have j0 := b1e164858 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e164858
      have b1e165249 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e10528 X0 X1 X0
           have i₂ := b1e164859 X0 X1
           grind)
        | exact superpose b1e164859 b1e10528
        | (have j0 := b1e10528 X0 X1 X0
           grind)
        | exact resolve b1e10528 b1e164859
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e10528
      have b1e165320 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (k X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e48056 X0 (M.op X0 X1)
           have i₂ := b1e164859 X0 X1
           grind)
        | exact superpose b1e164859 b1e48056
        | (have j0 := b1e48056 X0 (M.op X0 X1)
           grind)
        | exact resolve b1e48056 b1e164859
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e48056 b1e164859
      have b1e165410 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
        intro X0 X1
        first
        | (have j0 := b1e165320 X0 X1
           have j1 := b1e46567 X0 X1 X0
           grind)
        | (have r₁ := b1e165320 x X1
           have r₂ := b1e46567 x X1 x
           grind)
        | exact resolve b1e165320 b1e46567
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e46567 b1e165320
      have b1e166830 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x X0) x) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e74053 X0
           have i₂ := b1e165410 x X0
           grind)
        | exact superpose b1e165410 b1e74053
        | (have j0 := b1e74053 X0
           grind)
        | exact resolve b1e74053 b1e165410
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e74053 b1e165410
      have b1e166915 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x X0) y) ∨ (M.op X0 y) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b1e166830 X0
           have i₂ := b1e25 (M.op x X0)
           grind)
        | exact superpose b1e25 b1e166830
        | (have j0 := b1e166830 X0
           grind)
        | exact resolve b1e166830 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25 b1e166830
      have b1e183468 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 (k X1 X2)) := by
        intro X0 X1 X2
        first
        | (have j0 := b1e145489 X1 X2 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e145489
      have b1e183469 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (k X1 X2)) := by
        intro X0 X1 X2
        first
        | (have j0 := b1e183468 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e183468
      have b1e183963 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e183469 X2 (σ X0) (σ X1)
           have i₂ := b1e15 X0 X1
           grind)
        | exact superpose b1e15 b1e183469
        | exact resolve b1e183469 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e184016 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (τ (M.op X1 (σ x)))) := by
        intro X0 X1
        first
        | (have i₁ := b1e183469 X0 (τ (M.op X1 (σ x))) y
           have i₂ := b1e151653 X1
           grind)
        | exact superpose b1e151653 b1e183469
        | exact resolve b1e183469 b1e151653
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e151653 b1e183469
      have b1e185125 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (τ (M.op X1 (σ x)))) := by
        intro X0 X1
        first
        | (have i₁ := b1e184016 X0 X1
           have i₂ := b1e24 y X0 x
           grind)
        | exact superpose b1e24 b1e184016
        | exact resolve b1e184016 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e24 b1e184016
      have b1e187338 : ∀ X0 X1 : G, (M.op (σ (M.op (τ (M.op X0 (σ x))) y)) X1) = (M.op (σ (τ (M.op X0 (σ x)))) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e254 (τ (M.op X0 (σ x))) X1
           have i₂ := b1e185125 (τ (M.op X0 (σ x))) X0
           grind)
        | exact superpose b1e185125 b1e254
        | exact resolve b1e254 b1e185125
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e254 b1e185125
      have b1e187531 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ (M.op (τ (M.op X0 (σ x))) y)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e187338 X0 X1
           have i₂ := b1e12 (M.op X0 (σ x))
           grind)
        | exact superpose b1e12 b1e187338
        | exact resolve b1e187338 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e187338
      have b1e187634 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X1) = (M.op (M.op X0 (σ x)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e187531 X0 X1
           have i₂ := b1e151913 X0
           grind)
        | exact superpose b1e151913 b1e187531
        | exact resolve b1e187531 b1e151913
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e187531
      have b1e187669 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op X0 (σ x)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e187634 X0 X1
           have i₂ := b1e1515 X1
           grind)
        | exact superpose b1e1515 b1e187634
        | exact resolve b1e187634 b1e1515
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1515 b1e187634
      have b1e188472 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b1e165249 X0 (σ x)
           have i₂ := b1e187669 X0 X0
           grind)
        | exact superpose b1e187669 b1e165249
        | (have j0 := b1e165249 X0 (σ x)
           grind)
        | exact resolve b1e165249 b1e187669
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e165249
      have b1e188509 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ X0) (σ x)) = (σ (k x X0)) := by
        intro X0
        first
        | (have i₁ := b1e133691 X0 x
           have i₂ := b1e187669 (σ X0) (σ X0)
           grind)
        | exact superpose b1e187669 b1e133691
        | (have j0 := b1e133691 X0 x
           grind)
        | exact resolve b1e133691 b1e187669
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e133691
      have b1e188527 : (M.op (σ x) y) = (M.op x (σ x)) ∨ (M.op (σ x) y) = (k x (σ x)) := by
        first
        | (have i₁ := b1e166915 (σ x)
           have i₂ := b1e187669 x y
           grind)
        | exact superpose b1e187669 b1e166915
        | (have j0 := b1e166915 (σ x)
           grind)
        | exact resolve b1e166915 b1e187669
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e166915 b1e187669
      have b1e188984 : (M.op (σ x) y) = (k x (σ x)) := by
        first
        | (have j1 := b1e46678 (σ x)
           grind)
        | (have r₁ := b1e188527
           have r₂ := b1e46678 (σ x)
           grind)
        | exact resolve b1e188527 b1e46678
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e46678 b1e188527
      have b1e188986 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k x X0)) := by
        intro X0
        first
        | (have j0 := b1e188509 X0
           have j1 := b1e46855 X0 x
           grind)
        | (have r₁ := b1e188509 X0
           have r₂ := b1e46855 X0 x
           grind)
        | exact resolve b1e188509 b1e46855
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e46855 b1e188509
      have b1e189003 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
        intro X0
        first
        | (have j0 := b1e188472 X0
           have j1 := b1e44003 X0 (σ x)
           grind)
        | (have r₁ := b1e188472 x
           have r₂ := b1e44003 (σ x) x
           grind)
        | (have r₁ := b1e188472 X0
           have r₂ := b1e44003 X0 (σ x)
           grind)
        | exact resolve b1e188472 b1e44003
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e44003 b1e188472
      have b1e189372 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op (σ x) X0)) := by
        intro X0
        first
        | (have i₁ := b1e179 X0 x
           have i₂ := b1e189003 X0
           grind)
        | exact superpose b1e189003 b1e179
        | exact resolve b1e179 b1e189003
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e179
      have b1e190285 : ∀ X0 : G, (M.op x y) = (M.op (τ (σ (k x X0))) y) := by
        intro X0
        first
        | (have i₁ := b1e151913 (σ X0)
           have i₂ := b1e188986 X0
           grind)
        | exact superpose b1e188986 b1e151913
        | exact resolve b1e151913 b1e188986
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e151913 b1e188986
      have b1e190685 : ∀ X0 : G, (M.op x y) = (M.op (k x X0) y) := by
        intro X0
        first
        | (have i₁ := b1e190285 X0
           have i₂ := b1e11 (k x X0)
           grind)
        | exact superpose b1e11 b1e190285
        | exact resolve b1e190285 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e190285
      have b1e191121 : (M.op x y) = (M.op (M.op (σ x) y) y) := by
        first
        | (have i₁ := b1e190685 (σ x)
           have i₂ := b1e188984
           grind)
        | exact superpose b1e188984 b1e190685
        | exact resolve b1e190685 b1e188984
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e188984 b1e190685
      have b1e198228 : ∀ X0 X1 : G, (τ (M.op (σ x) (σ X0))) = (k (τ (σ (k X0 X1))) x) := by
        intro X0 X1
        first
        | (have i₁ := b1e189372 (σ (k X0 X1))
           have i₂ := b1e183963 X0 X1 (σ x)
           grind)
        | exact superpose b1e183963 b1e189372
        | exact resolve b1e189372 b1e183963
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e183963
      have b1e198518 : ∀ X0 X1 : G, (k (k X0 X1) x) = (τ (M.op (σ x) (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e198228 X0 X1
           have i₂ := b1e11 (k X0 X1)
           grind)
        | exact superpose b1e11 b1e198228
        | exact resolve b1e198228 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e198228
      have b1e198592 : ∀ X0 X1 : G, (k (k X0 X1) x) = (k (τ (σ X0)) x) := by
        intro X0 X1
        first
        | (have i₁ := b1e198518 X0 X1
           have i₂ := b1e189372 (σ X0)
           grind)
        | exact superpose b1e189372 b1e198518
        | exact resolve b1e198518 b1e189372
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e189372 b1e198518
      have b1e198640 : ∀ X0 X1 : G, (k X0 x) = (k (k X0 X1) x) := by
        intro X0 X1
        first
        | (have i₁ := b1e198592 X0 X1
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e198592
        | exact resolve b1e198592 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e198592
      have b1e199419 : ∀ X0 : G, (k X0 x) = (k (M.op (σ x) X0) x) := by
        intro X0
        first
        | (have i₁ := b1e198640 X0 (σ x)
           have i₂ := b1e189003 X0
           grind)
        | exact superpose b1e189003 b1e198640
        | exact resolve b1e198640 b1e189003
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e189003 b1e198640
      have b1e207678 : (k y x) = (M.op (M.op (σ x) y) y) := by
        first
        | (have i₁ := b1e10606 (σ x)
           have i₂ := b1e199419 y
           grind)
        | exact superpose b1e199419 b1e10606
        | exact resolve b1e10606 b1e199419
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e10606 b1e199419
      have b1e207831 : (M.op x y) = (k y x) := by
        first
        | (have i₁ := b1e207678
           have i₂ := b1e191121
           grind)
        | exact superpose b1e191121 b1e207678
        | exact resolve b1e207678 b1e191121
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e191121 b1e207678
      have b1e207912 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b1e207831
           have i₂ := b1e885
           grind)
        | exact superpose b1e885 b1e207831
        | exact resolve b1e207831 b1e885
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e885 b1e207831
      have b1e207966 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b1e1100
           have i₂ := b1e207912
           grind)
        | exact superpose b1e207912 b1e1100
        | exact resolve b1e1100 b1e207912
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1100 b1e207912
      have b1e208618 : False := by grind
      exact b1e208618
  · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X2 X1)) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b2e17 : (M.op y x) ≠ (M.op y y) := by grind
      have b2e18 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b2e20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X1 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e15
        | exact resolve b2e15 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e21 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 X1)) = (M.op (M.op X0 X0) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 (M.op X0 X0) X1 X2
           have i₂ := b2e10 X0 X0 X0
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e22 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X2 (M.op X3 X1) (M.op X0 X0)
           have i₂ := b2e10 X0 X1 X3
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e23 : ∀ X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op X3 X1)) := by
        intro X1 X2 X3
        first
        | (have i₁ := b2e22 x X1 X2 X3
           have i₂ := b2e10 X2 X1 x
           grind)
        | exact superpose b2e10 b2e22
        | exact resolve b2e22 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e22
      have b2e24 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e21 X0 X1 x
           have i₂ := b2e10 X0 X1 x
           grind)
        | exact superpose b2e10 b2e21
        | exact resolve b2e21 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21
      have b2e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X1) (M.op X3 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 (M.op X0 X1) X2 X3
           have i₂ := b2e23 X1 (M.op X0 X1) X0
           grind)
        | exact superpose b2e23 b2e10
        | exact resolve b2e10 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e32 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X1) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e28 X0 X1 X2 x
           have i₂ := b2e23 X2 (M.op (M.op X0 X1) X1) x
           grind)
        | exact superpose b2e23 b2e28
        | exact resolve b2e28 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e28
      have b2e36 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) := by
        intro X0
        first
        | (have i₁ := b2e10 X0 (σ x) (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e37 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b2e36 X0
           have i₂ := b2e10 X0 (σ y) (σ y)
           grind)
        | exact superpose b2e10 b2e36
        | exact resolve b2e36 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e36
      have b2e51 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X2 X1) (M.op X2 X1)) = (k (M.op X2 X1) (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e13 (M.op X2 X1) (M.op X0 X0)
           have i₂ := b2e10 X0 X1 X2
           grind)
        | exact superpose b2e10 b2e13
        | (have j0 := b2e13 (M.op X2 X1) (M.op X0 X0)
           grind)
        | exact resolve b2e13 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e52 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op X2 X1) (M.op X2 X1)) = (k (M.op X2 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e13 (M.op X2 X1) X0
           have i₂ := b2e23 X1 X0 X2
           grind)
        | exact superpose b2e23 b2e13
        | (have j0 := b2e13 X1 X0
           grind)
        | (have r₁ := b2e13 X1 (M.op x X1)
           have r₂ := b2e23 X1 (M.op x X1) x
           grind)
        | (have r₁ := b2e13 (M.op x X1) X1
           have r₂ := b2e23 X1 X1 x
           grind)
        | exact resolve b2e13 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e53 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
      have b2e55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e13 X1 (M.op X0 X0)
           have i₂ := b2e10 X0 X0 X0
           grind)
        | exact superpose b2e10 b2e13
        | (have j0 := b2e13 X1 (M.op X0 X0)
           grind)
        | exact resolve b2e13 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b2e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e59 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b2e53
      have b2e61 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e55 X0 X1
           have i₂ := b2e24 X0 X1
           grind)
        | exact superpose b2e24 b2e55
        | (have j0 := b2e55 X0 X1
           grind)
        | (have r₁ := b2e55 X1 X1
           have r₂ := b2e24 X1 X1
           grind)
        | exact resolve b2e55 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e55
      have b2e63 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b2e59
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e59
        | exact resolve b2e59 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e59
      have b2e64 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op X2 X1) X0) = (M.op (M.op X2 X1) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e52 X0 X1 X2
           have i₂ := b2e23 X1 (M.op X2 X1) X2
           grind)
        | exact superpose b2e23 b2e52
        | (have j0 := b2e52 X0 X1 X2
           grind)
        | (have r₁ := b2e52 (M.op x X1) X1 X2
           have r₂ := b2e23 X1 (M.op x X1) x
           grind)
        | (have r₁ := b2e52 X1 (M.op x X1) X2
           have r₂ := b2e23 X1 X1 x
           grind)
        | exact resolve b2e52 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e52
      have b2e65 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op X2 X1) (M.op X2 X1)) = (k (M.op X2 X1) (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e51 X0 X1 X2
           have i₂ := b2e10 X0 X0 X0
           grind)
        | exact superpose b2e10 b2e51
        | (have j0 := b2e51 X0 X1 X2
           grind)
        | (have r₁ := b2e51 X1 X1 X2
           have r₂ := b2e10 X1 X1 X1
           grind)
        | exact resolve b2e51 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e51
      have b2e67 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b2e63
           have i₂ := b2e37 (σ x)
           grind)
        | exact superpose b2e37 b2e63
        | exact resolve b2e63 b2e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e63
      have b2e68 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op X2 X1) (M.op X0 X0)) = (M.op (M.op X2 X1) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e65 X0 X1 X2
           have i₂ := b2e23 X1 (M.op X2 X1) X2
           grind)
        | exact superpose b2e23 b2e65
        | (have j0 := b2e65 X0 X1 X2
           grind)
        | (have r₁ := b2e65 (M.op x X1) X1 X2
           have r₂ := b2e23 X1 (M.op x X1) x
           grind)
        | (have r₁ := b2e65 X1 (M.op x X1) X2
           have r₂ := b2e23 X1 X1 x
           grind)
        | exact resolve b2e65 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e65
      have b2e70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b2e15 X0 X0
           have i₂ := b2e58 (σ X0)
           grind)
        | exact superpose b2e58 b2e15
        | exact resolve b2e15 b2e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b2e70 X0
           have i₂ := b2e58 X0
           grind)
        | exact superpose b2e58 b2e70
        | exact resolve b2e70 b2e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e70
      have b2e75 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X2 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e14 (M.op x X1) X2
           have i₂ := b2e23 X1 X2 x
           grind)
        | exact superpose b2e23 b2e14
        | (have j0 := b2e14 X1 X0
           grind)
        | exact resolve b2e14 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e13 X1 X0
           have i₂ := b2e14 X1 X0
           grind)
        | (have i₁ := b2e13 X1 X1
           have i₂ := b2e14 X0 X1
           grind)
        | exact superpose b2e14 b2e13
        | (have j0 := b2e13 X0 X0
           have j1 := b2e14 X1 X0
           grind)
        | (have r₁ := b2e13 X0 X1
           have r₂ := b2e14 X0 X1
           grind)
        | (have r₁ := b2e13 X0 X0
           have r₂ := b2e14 X0 X0
           grind)
        | exact resolve b2e13 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e88 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) X2) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e24 X0 X2
           have i₂ := b2e14 X1 X0
           grind)
        | (have i₁ := b2e24 X0 X1
           have i₂ := b2e14 X0 X0
           grind)
        | exact superpose b2e14 b2e24
        | (have j1 := b2e14 X1 X0
           grind)
        | exact resolve b2e24 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e92 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 X1)) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 X2 X0 X0
           have i₂ := b2e14 X1 X0
           grind)
        | (have i₁ := b2e10 X0 X0 X1
           have i₂ := b2e14 X0 X1
           grind)
        | exact superpose b2e14 b2e10
        | (have j1 := b2e14 X1 X0
           grind)
        | exact resolve b2e10 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e96 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X1 X0
           have i₂ := b2e14 (σ X1) (σ X0)
           grind)
        | exact superpose b2e14 b2e15
        | (have j1 := b2e14 (σ X1) (σ X0)
           grind)
        | exact resolve b2e15 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e98 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b2e81 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e81
      have b2e99 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e96 X0 X1
           have i₂ := b2e71 X0
           grind)
        | exact superpose b2e71 b2e96
        | (have j0 := b2e96 X0 X1
           grind)
        | exact resolve b2e96 b2e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e96
      have b2e102 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e92 X0 X1 X2
           have i₂ := b2e10 X2 X1 X0
           grind)
        | exact superpose b2e10 b2e92
        | (have j0 := b2e92 X0 X1 X2
           grind)
        | exact resolve b2e92 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e92
      have b2e128 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e13 X0 (σ x)
           have i₂ := b2e37 (σ x)
           grind)
        | exact superpose b2e37 b2e13
        | (have j0 := b2e13 X0 (σ x)
           grind)
        | (have r₁ := b2e13 (σ x) (σ y)
           have r₂ := b2e37 (σ y)
           grind)
        | (have r₁ := b2e13 (σ y) (σ x)
           have r₂ := b2e37 (σ x)
           grind)
        | exact resolve b2e13 b2e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e142 : ∀ X0 : G, (σ (k x y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e128 X0
           have i₂ := b2e67
           grind)
        | exact superpose b2e67 b2e128
        | (have j0 := b2e128 X0
           grind)
        | exact resolve b2e128 b2e67
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e128
      have b2e149 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b2e19 X0 (τ X0)
           have i₂ := b2e58 (τ X0)
           grind)
        | exact superpose b2e58 b2e19
        | exact resolve b2e19 b2e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e153 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e11 (k (τ X0) X1)
           have i₂ := b2e19 X0 X1
           grind)
        | exact superpose b2e19 b2e11
        | exact resolve b2e11 b2e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19
      have b2e154 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b2e149 X0
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e149
        | exact resolve b2e149 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e149
      have b2e155 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b2e154 X0
           have i₂ := b2e58 X0
           grind)
        | exact superpose b2e58 b2e154
        | exact resolve b2e154 b2e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58 b2e154
      have b2e163 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e11 (k X0 (τ X1))
           have i₂ := b2e20 X1 X0
           grind)
        | exact superpose b2e20 b2e11
        | exact resolve b2e11 b2e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e168 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e67
           grind)
        | exact superpose b2e67 b2e16
        | exact resolve b2e16 b2e67
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e172 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ (M.op y x) = (M.op y y) := by
        first
        | (have i₁ := b2e168
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e168
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e168 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e168
      have b2e173 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
        first
        | (have r₁ := b2e172
           have r₂ := b2e17
           grind)
        | exact resolve b2e172 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e172
      have b2e201 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b2e98 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e250 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X2) ∨ (M.op X2 X0) = (k X0 X2) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e98 X2 X0
           have i₂ := b2e102 X1 X0 X0
           grind)
        | (have i₁ := b2e98 X0 X0
           have i₂ := b2e102 X0 X1 X0
           grind)
        | exact superpose b2e102 b2e98
        | (have j0 := b2e98 X2 X0
           have j1 := b2e102 X2 X0 X2
           grind)
        | exact resolve b2e98 b2e102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e98
      have b2e252 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X2 X2) = (k X2 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e13 X2 X0
           have i₂ := b2e102 X1 X0 X0
           grind)
        | (have i₁ := b2e13 X0 X0
           have i₂ := b2e102 X0 X1 X0
           grind)
        | exact superpose b2e102 b2e13
        | (have j0 := b2e13 X2 X0
           have j1 := b2e102 X1 X0 X2
           grind)
        | (have r₁ := b2e13 X1 X0
           have r₂ := b2e102 X0 X1 X0
           grind)
        | (have r₁ := b2e13 X0 X1
           have r₂ := b2e102 X0 X1 X1
           grind)
        | exact resolve b2e13 b2e102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e253 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) X2) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e24 X0 X2
           have i₂ := b2e102 X1 X0 X0
           grind)
        | (have i₁ := b2e24 X0 X1
           have i₂ := b2e102 X0 X1 X0
           grind)
        | exact superpose b2e102 b2e24
        | (have j1 := b2e102 X1 X0 X2
           grind)
        | exact resolve b2e24 b2e102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e255 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X2 X0) ∨ (M.op X1 X2) = (k X2 X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e14 X1 X2
           have i₂ := b2e102 X0 X1 X2
           grind)
        | (have i₁ := b2e14 X0 X2
           have i₂ := b2e102 X0 X1 X2
           grind)
        | exact superpose b2e102 b2e14
        | (have j0 := b2e14 X1 X0
           have j1 := b2e102 X0 X1 X0
           grind)
        | exact resolve b2e14 b2e102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e259 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X1 (M.op X3 X2)) = (k (M.op X3 X2) X1) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e23 X2 X0 X3
           have i₂ := b2e102 X1 (M.op X3 X2) X0
           grind)
        | (have i₁ := b2e23 X1 X2 X3
           have i₂ := b2e102 (M.op X3 X1) X1 X2
           grind)
        | exact superpose b2e102 b2e23
        | (have j1 := b2e102 X2 X1 X0
           grind)
        | exact resolve b2e23 b2e102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e296 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (k (M.op X3 X2) X1) ∨ (M.op X0 X1) = (M.op X0 X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e259 X0 X1 X2 X3
           have i₂ := b2e23 X2 X1 X3
           grind)
        | exact superpose b2e23 b2e259
        | (have j0 := b2e259 X0 X1 X2 X3
           grind)
        | exact resolve b2e259 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e259
      have b2e313 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e71 (k X1 (τ X0))
           have i₂ := b2e20 X0 X1
           grind)
        | exact superpose b2e20 b2e71
        | exact resolve b2e71 b2e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e20
      have b2e319 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b2e37 (σ x)
           have i₂ := b2e71 x
           grind)
        | exact superpose b2e71 b2e37
        | exact resolve b2e37 b2e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e323 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e24 (σ X0) X1
           have i₂ := b2e71 X0
           grind)
        | exact superpose b2e71 b2e24
        | exact resolve b2e24 b2e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e328 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e23 (σ X0) X1 (σ X0)
           have i₂ := b2e71 X0
           grind)
        | exact superpose b2e71 b2e23
        | exact resolve b2e23 b2e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e335 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e61 X1 X0
           have i₂ := b2e14 X0 X1
           grind)
        | (have i₁ := b2e61 X1 X1
           have i₂ := b2e14 X0 X1
           grind)
        | exact superpose b2e14 b2e61
        | (have j1 := b2e14 X1 X0
           grind)
        | (have r₁ := b2e61 X1 X0
           have r₂ := b2e14 X0 X1
           grind)
        | (have r₁ := b2e61 X0 X0
           have r₂ := b2e14 X0 X0
           grind)
        | exact resolve b2e61 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e61
      have b2e358 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b2e335 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e335
      have b2e449 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e153 X1 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e153
        | exact resolve b2e153 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e486 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have j0 := b2e68 X1 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e68
      have b2e530 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) ∨ (M.op (σ X0) (σ X2)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e99 X0 X2
           have i₂ := b2e102 X0 X1 X0
           grind)
        | (have i₁ := b2e99 X1 X1
           have i₂ := b2e102 X0 X1 X1
           grind)
        | exact superpose b2e102 b2e99
        | (have j0 := b2e99 X0 X2
           have j1 := b2e102 X0 X1 X2
           grind)
        | exact resolve b2e99 b2e102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e102
      have b2e608 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e23 (σ X0) X2 (σ X1)
           have i₂ := b2e99 X1 X0
           grind)
        | exact superpose b2e99 b2e23
        | (have j1 := b2e99 X1 X0
           grind)
        | exact resolve b2e23 b2e99
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e614 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b2e99 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e99
      have b2e872 : (σ (k x y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b2e67
           have i₂ := b2e319
           grind)
        | exact superpose b2e319 b2e67
        | exact resolve b2e67 b2e319
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e873 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e319
           grind)
        | exact superpose b2e319 b2e16
        | exact resolve b2e16 b2e319
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e319
      have b2e952 : (σ (M.op x x)) = (σ (M.op y x)) ∨ (M.op y x) = (M.op y y) := by
        first
        | (have i₁ := b2e872
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e872
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e872 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e954 : (k x y) = (τ (σ (M.op x x))) := by
        first
        | (have i₁ := b2e11 (k x y)
           have i₂ := b2e872
           grind)
        | exact superpose b2e872 b2e11
        | exact resolve b2e11 b2e872
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e973 : (k x y) = (M.op x x) := by
        first
        | (have i₁ := b2e954
           have i₂ := b2e11 (M.op x x)
           grind)
        | exact superpose b2e11 b2e954
        | exact resolve b2e954 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e954
      have b2e974 : (σ (M.op x x)) = (σ (M.op y x)) := by
        first
        | (have r₁ := b2e952
           have r₂ := b2e17
           grind)
        | exact resolve b2e952 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e952
      have b2e1225 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) := by
        first
        | (have i₁ := b2e14 x y
           have i₂ := b2e973
           grind)
        | exact superpose b2e973 b2e14
        | (have j0 := b2e14 x y
           grind)
        | exact resolve b2e14 b2e973
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e973
      have b2e1226 : (M.op y x) = (M.op x x) := by
        first
        | (have r₁ := b2e1225
           have r₂ := b2e17
           grind)
        | exact resolve b2e1225 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1225
      have b2e1429 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y x) X0) := by
        intro X0
        first
        | (have i₁ := b2e24 x X0
           have i₂ := b2e1226
           grind)
        | exact superpose b2e1226 b2e24
        | exact resolve b2e24 b2e1226
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1667 : (M.op (M.op (σ y) (σ y)) (σ x)) = (k (M.op (σ y) (σ y)) (M.op (σ x) (σ x))) := by
        first
        | (have i₁ := b2e486 (σ y) (σ x)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e486
        | exact resolve b2e486 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e486
      have b2e1721 : (M.op (M.op (σ y) (σ y)) (σ x)) = (k (M.op (σ y) (σ y)) (σ (M.op x x))) := by
        first
        | (have i₁ := b2e1667
           have i₂ := b2e71 x
           grind)
        | exact superpose b2e71 b2e1667
        | exact resolve b2e1667 b2e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1667
      have b2e1750 : (M.op (M.op (σ y) (σ y)) (σ x)) = (k (M.op (σ y) (σ y)) (σ (M.op y x))) := by
        first
        | (have i₁ := b2e1721
           have i₂ := b2e974
           grind)
        | exact superpose b2e974 b2e1721
        | exact resolve b2e1721 b2e974
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1721
      have b2e1769 : (M.op (σ (M.op y y)) (σ x)) = (k (σ (M.op y y)) (σ (M.op y x))) := by
        first
        | (have i₁ := b2e1750
           have i₂ := b2e71 y
           grind)
        | exact superpose b2e71 b2e1750
        | exact resolve b2e1750 b2e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1750
      have b2e1777 : (M.op (σ (M.op y y)) (σ x)) = (σ (k (M.op y y) (M.op y x))) := by
        first
        | (have i₁ := b2e1769
           have i₂ := b2e15 (M.op y y) (M.op y x)
           grind)
        | exact superpose b2e15 b2e1769
        | exact resolve b2e1769 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1769
      have b2e1784 : (M.op (σ y) (σ x)) = (σ (k (M.op y y) (M.op y x))) := by
        first
        | (have i₁ := b2e1777
           have i₂ := b2e323 y (σ x)
           grind)
        | exact superpose b2e323 b2e1777
        | exact resolve b2e1777 b2e323
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e323 b2e1777
      have b2e1790 : (M.op (σ y) (σ y)) = (σ (k (M.op y y) (M.op y x))) := by
        first
        | (have i₁ := b2e1784
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e1784
        | exact resolve b2e1784 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1784
      have b2e1794 : (σ (M.op y y)) = (σ (k (M.op y y) (M.op y x))) := by
        first
        | (have i₁ := b2e1790
           have i₂ := b2e71 y
           grind)
        | exact superpose b2e71 b2e1790
        | exact resolve b2e1790 b2e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1790
      have b2e1838 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X0 X0)) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e201 (M.op X0 X0) X1
           have i₂ := b2e10 X0 X0 X0
           grind)
        | exact superpose b2e10 b2e201
        | (have j0 := b2e201 (M.op X0 X0) X1
           grind)
        | exact resolve b2e201 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1840 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e201 (σ X0) X1
           have i₂ := b2e71 X0
           grind)
        | exact superpose b2e71 b2e201
        | (have j0 := b2e201 (σ X0) X1
           grind)
        | exact resolve b2e201 b2e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1885 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e1838 X0 X1
           have i₂ := b2e23 X0 X1 X0
           grind)
        | exact superpose b2e23 b2e1838
        | (have j0 := b2e1838 X0 X1
           grind)
        | (have r₁ := b2e1838 x x
           have r₂ := b2e23 x x x
           grind)
        | exact resolve b2e1838 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1838
      have b2e1898 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e1885 X0 X1
           have i₂ := b2e23 X0 X1 X0
           grind)
        | exact superpose b2e23 b2e1885
        | (have j0 := b2e1885 X0 X1
           grind)
        | exact resolve b2e1885 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1885
      have b2e6289 : (k (M.op y y) (M.op y x)) = (τ (σ (M.op y y))) := by
        first
        | (have i₁ := b2e11 (k (M.op y y) (M.op y x))
           have i₂ := b2e1794
           grind)
        | exact superpose b2e1794 b2e11
        | exact resolve b2e11 b2e1794
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e6324 : (M.op y y) = (k (M.op y y) (M.op y x)) := by
        first
        | (have i₁ := b2e6289
           have i₂ := b2e11 (M.op y y)
           grind)
        | exact superpose b2e11 b2e6289
        | exact resolve b2e6289 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e6289
      have b2e6393 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (k (M.op X2 X1) (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e358 (M.op X0 X0) (M.op X2 X1)
           have i₂ := b2e10 X0 X1 X2
           grind)
        | exact superpose b2e10 b2e358
        | exact resolve b2e358 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e358
      have b2e6455 : ∀ X0 : G, (M.op y y) = (M.op (M.op y x) y) ∨ (M.op X0 y) = (M.op X0 (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b2e296 X0 (M.op y x) y y
           have i₂ := b2e6324
           grind)
        | exact superpose b2e6324 b2e296
        | (have j0 := b2e296 X0 y (M.op y x) x
           grind)
        | exact resolve b2e296 b2e6324
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e296 b2e6324
      have b2e6468 : ∀ X0 : G, (M.op x y) = (M.op y y) ∨ (M.op X0 y) = (M.op X0 (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b2e6455 X0
           have i₂ := b2e1429 y
           grind)
        | exact superpose b2e1429 b2e6455
        | (have j0 := b2e6455 X0
           grind)
        | exact resolve b2e6455 b2e1429
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1429 b2e6455
      have b2e6481 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op x y) = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b2e6468 X0
           have i₂ := b2e23 x X0 y
           grind)
        | exact superpose b2e23 b2e6468
        | exact resolve b2e6468 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e6468
      have b2e7487 : (σ (k x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b2e142 (σ y)
           have i₂ := b2e67
           grind)
        | exact superpose b2e67 b2e142
        | (have j0 := b2e142 (σ y)
           grind)
        | (have r₁ := b2e142 (σ y)
           have r₂ := b2e67
           grind)
        | exact resolve b2e142 b2e67
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e142
      have b2e7491 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by grind
      clear b2e7487
      have b2e7495 : (M.op (σ y) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b2e7491
           have i₂ := b2e15 y x
           grind)
        | exact superpose b2e15 b2e7491
        | exact resolve b2e7491 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e7491
      have b2e7512 : (σ (M.op y y)) = (σ (k y x)) := by
        first
        | (have i₁ := b2e7495
           have i₂ := b2e71 y
           grind)
        | exact superpose b2e71 b2e7495
        | exact resolve b2e7495 b2e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e7495
      have b2e7559 : (k y x) = (τ (σ (M.op y y))) := by
        first
        | (have i₁ := b2e11 (k y x)
           have i₂ := b2e7512
           grind)
        | exact superpose b2e7512 b2e11
        | exact resolve b2e11 b2e7512
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e7594 : (M.op y y) = (k y x) := by
        first
        | (have i₁ := b2e7559
           have i₂ := b2e11 (M.op y y)
           grind)
        | exact superpose b2e11 b2e7559
        | exact resolve b2e7559 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e7559
      have b2e8881 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) := by
        intro X0 X1
        first
        | (have j0 := b2e64 X1 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e64
      have b2e9038 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ x)) = (k (M.op X0 (σ y)) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e8881 X0 (σ x)
           have i₂ := b2e37 X0
           grind)
        | exact superpose b2e37 b2e8881
        | exact resolve b2e8881 b2e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e9070 : ∀ X0 X1 : G, (k (τ (M.op X0 (σ X1))) X1) = (τ (M.op (M.op X0 (σ X1)) (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e153 (M.op X0 (σ X1)) X1
           have i₂ := b2e8881 X0 (σ X1)
           grind)
        | exact superpose b2e8881 b2e153
        | exact resolve b2e153 b2e8881
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e9091 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (k (M.op X0 (σ y)) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e9038 X0
           have i₂ := b2e37 (M.op X0 (σ y))
           grind)
        | exact superpose b2e37 b2e9038
        | exact resolve b2e9038 b2e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e9038
      have b2e21296 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e614 (τ X0) (τ X1)
           have i₂ := b2e449 X0 X1
           grind)
        | exact superpose b2e449 b2e614
        | exact resolve b2e614 b2e449
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e614
      have b2e21344 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e21296 X0 X1
           have i₂ := b2e155 X1
           grind)
        | exact superpose b2e155 b2e21296
        | (have j0 := b2e21296 X0 X1
           grind)
        | exact resolve b2e21296 b2e155
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21296
      have b2e21417 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e21344 X0 X1
           have i₂ := b2e12 (k X0 X1)
           grind)
        | exact superpose b2e12 b2e21344
        | (have j0 := b2e21344 X0 X1
           grind)
        | exact resolve b2e21344 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21344
      have b2e21476 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e21417 X0 X1
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e21417
        | (have j0 := b2e21417 X0 X1
           grind)
        | exact resolve b2e21417 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21417
      have b2e21520 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e21476 X0 X1
           have i₂ := b2e12 X1
           grind)
        | exact superpose b2e12 b2e21476
        | (have j0 := b2e21476 X0 X1
           grind)
        | exact resolve b2e21476 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21476
      have b2e21551 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e21520 X0 X1
           have i₂ := b2e12 (k X0 X1)
           grind)
        | exact superpose b2e12 b2e21520
        | (have j0 := b2e21520 X0 X1
           grind)
        | exact resolve b2e21520 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21520
      have b2e37347 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b2e873
           have i₂ := b2e6481 x
           grind)
        | exact superpose b2e6481 b2e873
        | exact resolve b2e873 b2e6481
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e873 b2e6481
      have b2e37380 : (M.op x y) = (M.op y y) := by grind
      clear b2e37347
      have b2e38664 : (σ (M.op y x)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b2e173
           have i₂ := b2e37380
           grind)
        | exact superpose b2e37380 b2e173
        | exact resolve b2e173 b2e37380
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e173
      have b2e40863 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b2e250 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e40867 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b2e250 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e250
      have b2e40868 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b2e40867 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e40867
      have b2e40870 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b2e40863 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e40863
      have b2e41760 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e21551 X0 X1
           have i₂ := b2e40868 X0 X1
           grind)
        | exact superpose b2e40868 b2e21551
        | (have j0 := b2e21551 X0 X1
           have j1 := b2e40868 X0 X1
           grind)
        | (have r₁ := b2e21551 X1 X1
           have r₂ := b2e40868 X1 X1
           grind)
        | (have r₁ := b2e21551 X0 X0
           have r₂ := b2e40868 X0 X0
           grind)
        | exact resolve b2e21551 b2e40868
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21551
      have b2e42010 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b2e41760 X0 X1
           have j1 := b2e40870 X0 X1
           grind)
        | (have r₁ := b2e41760 X0 X1
           have r₂ := b2e40870 X0 X1
           grind)
        | (have r₁ := b2e41760 X1 X0
           have r₂ := b2e40870 X0 X1
           grind)
        | exact resolve b2e41760 b2e40870
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e41760
      have b2e43798 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b2e252 X1 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e252
      have b2e44041 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X1) X0) ∨ (M.op (M.op X2 X1) X0) = (k X0 (M.op X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e40870 X0 (M.op X2 X1)
           have i₂ := b2e23 X1 X0 X2
           grind)
        | exact superpose b2e23 b2e40870
        | (have j0 := b2e40870 X0 (M.op X2 X1)
           grind)
        | exact resolve b2e40870 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e40870
      have b2e45001 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (k X2 X1) ∨ (M.op X1 X1) = (M.op X1 X2) ∨ (M.op X2 X0) = (k X0 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e14 X1 X0
           have i₂ := b2e255 X0 X1 X2
           grind)
        | exact superpose b2e255 b2e14
        | (have j0 := b2e14 X2 X1
           have j1 := b2e255 X1 X2 X0
           grind)
        | exact resolve b2e14 b2e255
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e45369 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (k X2 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X2) = (k X2 X1) := by
        intro X0 X1 X2
        first
        | (have j0 := b2e255 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e255
      have b2e45538 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X2 X1) ∨ (M.op X1 X1) = (M.op X1 X2) ∨ (M.op X2 X0) = (k X0 X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b2e45001 X0 X1 X2
           have j1 := b2e45369 X1 X2 X0
           grind)
        | (have r₁ := b2e45001 X2 X0 X2
           have r₂ := b2e45369 X0 X1 X2
           grind)
        | (have r₁ := b2e45001 X2 X1 X2
           have r₂ := b2e45369 X2 X1 X2
           grind)
        | exact resolve b2e45001 b2e45369
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e45001 b2e45369
      have b2e46531 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e43798 X1 X0
           have i₂ := b2e40868 X1 X0
           grind)
        | exact superpose b2e40868 b2e43798
        | (have j0 := b2e43798 X1 X0
           have j1 := b2e40868 X1 X0
           grind)
        | exact resolve b2e43798 b2e40868
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e40868 b2e43798
      have b2e47167 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b2e46531 X0 X1
           have j1 := b2e42010 X0 X1
           grind)
        | (have r₁ := b2e46531 X0 X1
           have r₂ := b2e42010 X0 X1
           grind)
        | (have r₁ := b2e46531 X0 X0
           have r₂ := b2e42010 X0 X0
           grind)
        | exact resolve b2e46531 b2e42010
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46531
      have b2e53636 : ∀ X0 X1 X2 : G, (M.op X2 (σ (τ X0))) = (M.op X2 (σ (τ (k X0 X1)))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e608 (τ X0) (τ X1) X2
           have i₂ := b2e449 X1 X0
           grind)
        | exact superpose b2e449 b2e608
        | (have j0 := b2e608 (τ X0) (τ X1) X2
           grind)
        | exact resolve b2e608 b2e449
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e449 b2e608
      have b2e54497 : ∀ X0 X1 X2 : G, (M.op X2 (k X0 X1)) = (M.op X2 (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e53636 X0 X1 X2
           have i₂ := b2e12 (k X0 X1)
           grind)
        | exact superpose b2e12 b2e53636
        | (have j0 := b2e53636 X0 X1 X2
           grind)
        | exact resolve b2e53636 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e53636
      have b2e54638 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (k X0 X1)) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e54497 X0 X1 X2
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e54497
        | (have j0 := b2e54497 X0 X1 X2
           grind)
        | exact resolve b2e54497 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54497
      have b2e54725 : ∀ X0 X1 X2 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e54638 X0 X1 X2
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e54638
        | (have j0 := b2e54638 X0 X1 X2
           grind)
        | exact resolve b2e54638 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54638
      have b2e54776 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e54725 X0 X1 X2
           have i₂ := b2e12 X1
           grind)
        | exact superpose b2e12 b2e54725
        | (have j0 := b2e54725 X0 X1 X2
           grind)
        | exact resolve b2e54725 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54725
      have b2e54813 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X2 X0) = (M.op X2 (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e54776 X0 X1 X2
           have i₂ := b2e155 X1
           grind)
        | exact superpose b2e155 b2e54776
        | (have j0 := b2e54776 X0 X1 X2
           grind)
        | exact resolve b2e54776 b2e155
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e155 b2e54776
      have b2e79714 : ∀ X0 : G, (τ (M.op (M.op X0 (σ y)) (σ y))) = (k (τ (M.op X0 (σ y))) x) := by
        intro X0
        first
        | (have i₁ := b2e153 (M.op X0 (σ y)) x
           have i₂ := b2e9091 X0
           grind)
        | exact superpose b2e9091 b2e153
        | exact resolve b2e153 b2e9091
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e9091
      have b2e79715 : ∀ X0 : G, (k (τ (M.op X0 (σ y))) x) = (k (τ (M.op X0 (σ y))) y) := by
        intro X0
        first
        | (have i₁ := b2e79714 X0
           have i₂ := b2e9070 X0 y
           grind)
        | exact superpose b2e9070 b2e79714
        | exact resolve b2e79714 b2e9070
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e9070 b2e79714
      have b2e87044 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x X0)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x X0) = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b2e16
           have i₂ := b2e530 x X0 y
           grind)
        | exact superpose b2e530 b2e16
        | (have j1 := b2e530 x X0 y
           grind)
        | (have r₁ := b2e16
           have r₂ := b2e530 x y y
           grind)
        | exact resolve b2e16 b2e530
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e530
      have b2e87295 : ∀ X0 : G, (σ (M.op x X0)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x X0) = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b2e87044 X0
           have i₂ := b2e37380
           grind)
        | exact superpose b2e37380 b2e87044
        | (have j0 := b2e87044 X0
           grind)
        | exact resolve b2e87044 b2e37380
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e87044
      have b2e87324 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x X0)) ≠ (σ (M.op y y)) ∨ (M.op x X0) = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b2e87295 X0
           have i₂ := b2e7512
           grind)
        | exact superpose b2e7512 b2e87295
        | (have j0 := b2e87295 X0
           grind)
        | exact resolve b2e87295 b2e7512
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e7512 b2e87295
      have b2e87345 : ∀ X0 : G, (σ (k x y)) = (σ (M.op y y)) ∨ (σ (M.op x X0)) ≠ (σ (M.op y y)) ∨ (M.op x X0) = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b2e87324 X0
           have i₂ := b2e67
           grind)
        | exact superpose b2e67 b2e87324
        | (have j0 := b2e87324 X0
           grind)
        | exact resolve b2e87324 b2e67
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e67 b2e87324
      have b2e87359 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x X0)) ≠ (σ (M.op y y)) ∨ (M.op x X0) = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b2e87345 X0
           have i₂ := b2e872
           grind)
        | exact superpose b2e872 b2e87345
        | (have j0 := b2e87345 X0
           grind)
        | exact resolve b2e87345 b2e872
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e872 b2e87345
      have b2e87368 : ∀ X0 : G, (σ (M.op y x)) = (σ (M.op y y)) ∨ (σ (M.op x X0)) ≠ (σ (M.op y y)) ∨ (M.op x X0) = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b2e87359 X0
           have i₂ := b2e974
           grind)
        | exact superpose b2e974 b2e87359
        | (have j0 := b2e87359 X0
           grind)
        | exact resolve b2e87359 b2e974
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e974 b2e87359
      have b2e87376 : ∀ X0 : G, (σ (M.op x X0)) ≠ (σ (M.op y y)) ∨ (M.op x X0) = (k X0 x) := by
        intro X0
        first
        | (have j0 := b2e87368 X0
           grind)
        | (have r₁ := b2e87368 X0
           have r₂ := b2e38664
           grind)
        | exact resolve b2e87368 b2e38664
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e87368
      have b2e109906 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k (M.op X2 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e1898 X1 X0
           have i₂ := b2e75 X0 X1 X2
           grind)
        | (have i₁ := b2e1898 X0 X0
           have i₂ := b2e75 X0 X1 X2
           grind)
        | exact superpose b2e75 b2e1898
        | (have j1 := b2e75 X0 X1 X0
           grind)
        | (have r₁ := b2e1898 X1 X1
           have r₂ := b2e75 X1 X1 X2
           grind)
        | exact resolve b2e1898 b2e75
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e75 b2e1898
      have b2e109954 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = (k (M.op X2 X1) X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b2e109906 X0 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e109906
      have b2e123242 : ∀ X0 X1 : G, (σ (M.op x X0)) ≠ (σ (M.op y y)) ∨ (M.op x X0) = (k (M.op X1 X0) x) := by
        intro X0 X1
        first
        | (have i₁ := b2e87376 (M.op x X1)
           have i₂ := b2e23 X1 x x
           grind)
        | exact superpose b2e23 b2e87376
        | (have j0 := b2e87376 X0
           grind)
        | exact resolve b2e87376 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e87376
      have b2e127984 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X1) = (M.op X2 (k X1 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e13 X1 X0
           have i₂ := b2e54813 X1 X0 X2
           grind)
        | (have i₁ := b2e13 X1 X1
           have i₂ := b2e54813 X0 X1 X2
           grind)
        | exact superpose b2e54813 b2e13
        | (have j0 := b2e13 X0 X0
           have j1 := b2e54813 X1 X0 X2
           grind)
        | (have r₁ := b2e13 X0 X1
           have r₂ := b2e54813 X0 X1 X2
           grind)
        | (have r₁ := b2e13 X0 X0
           have r₂ := b2e54813 X0 X0 X2
           grind)
        | (have r₁ := b2e13 X0 (k X0 X1)
           have r₂ := b2e54813 X0 X1 (k X0 X1)
           grind)
        | exact resolve b2e13 b2e54813
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54813
      have b2e128122 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X1) = (M.op X2 (k X1 X0)) := by
        intro X0 X1 X2
        first
        | (have j0 := b2e127984 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e127984
      have b2e131603 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X2 (k X0 X1)) ∨ (M.op X3 X0) = (M.op X3 (k X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e23 X0 X2 X0
           have i₂ := b2e128122 X1 X0 X3
           grind)
        | exact superpose b2e128122 b2e23
        | (have j1 := b2e128122 X1 X0 X2
           grind)
        | exact resolve b2e23 b2e128122
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e128122
      have b2e150861 : ∀ X0 : G, (M.op y y) = (k X0 x) ∨ (M.op x y) = (M.op x x) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b2e7594
           have i₂ := b2e45538 X0 x y
           grind)
        | (have i₁ := b2e7594
           have i₂ := b2e45538 y x x
           grind)
        | exact superpose b2e45538 b2e7594
        | (have j1 := b2e45538 X0 x y
           grind)
        | exact resolve b2e7594 b2e45538
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e7594 b2e45538
      have b2e150865 : ∀ X0 : G, (M.op x y) = (M.op y x) ∨ (M.op y y) = (k X0 x) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b2e150861 X0
           have i₂ := b2e1226
           grind)
        | exact superpose b2e1226 b2e150861
        | (have j0 := b2e150861 X0
           grind)
        | exact resolve b2e150861 b2e1226
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e150861
      have b2e150875 : ∀ X0 : G, (M.op y x) = (M.op y y) ∨ (M.op y y) = (k X0 x) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b2e150865 X0
           have i₂ := b2e37380
           grind)
        | exact superpose b2e37380 b2e150865
        | (have j0 := b2e150865 X0
           grind)
        | exact resolve b2e150865 b2e37380
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e150865
      have b2e150879 : ∀ X0 : G, (M.op y y) = (k X0 x) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have j0 := b2e150875 X0
           grind)
        | (have r₁ := b2e150875 X0
           have r₂ := b2e17
           grind)
        | exact resolve b2e150875 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e150875
      have b2e153393 : ∀ X0 : G, (M.op y y) = (k (M.op x x) (M.op y y)) ∨ (M.op y y) = (k (M.op X0 y) (M.op x x)) := by
        intro X0
        first
        | (have i₁ := b2e6393 x y x
           have i₂ := b2e37380
           grind)
        | exact superpose b2e37380 b2e6393
        | exact resolve b2e6393 b2e37380
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e153409 : ∀ X0 : G, (σ (M.op y x)) = (σ (M.op y y)) ∨ (M.op y x) = (k (M.op X0 x) (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b2e1794
           have i₂ := b2e6393 y x X0
           grind)
        | exact superpose b2e6393 b2e1794
        | (have j1 := b2e6393 y x X0
           grind)
        | exact resolve b2e1794 b2e6393
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1794 b2e6393
      have b2e153422 : ∀ X0 : G, (M.op y x) = (k (M.op X0 x) (M.op y y)) := by
        intro X0
        first
        | (have j0 := b2e153409 X0
           grind)
        | (have r₁ := b2e153409 X0
           have r₂ := b2e38664
           grind)
        | exact resolve b2e153409 b2e38664
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e153409
      have b2e153425 : ∀ X0 : G, (M.op y y) = (k (M.op y x) (M.op y y)) ∨ (M.op y y) = (k (M.op X0 y) (M.op x x)) := by
        intro X0
        first
        | (have i₁ := b2e153393 X0
           have i₂ := b2e1226
           grind)
        | exact superpose b2e1226 b2e153393
        | (have j0 := b2e153393 X0
           grind)
        | exact resolve b2e153393 b2e1226
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e153393
      have b2e153427 : ∀ X0 : G, (M.op y x) = (M.op y y) ∨ (M.op y y) = (k (M.op X0 y) (M.op x x)) := by
        intro X0
        first
        | (have i₁ := b2e153425 X0
           have i₂ := b2e153422 y
           grind)
        | exact superpose b2e153422 b2e153425
        | (have j0 := b2e153425 X0
           grind)
        | exact resolve b2e153425 b2e153422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e153422 b2e153425
      have b2e153429 : ∀ X0 : G, (M.op y y) = (k (M.op X0 y) (M.op x x)) := by
        intro X0
        first
        | (have j0 := b2e153427 X0
           grind)
        | (have r₁ := b2e153427 X0
           have r₂ := b2e17
           grind)
        | exact resolve b2e153427 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e153427
      have b2e153431 : ∀ X0 : G, (M.op y y) = (k (M.op X0 y) (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b2e153429 X0
           have i₂ := b2e1226
           grind)
        | exact superpose b2e1226 b2e153429
        | exact resolve b2e153429 b2e1226
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1226 b2e153429
      have b2e155929 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
        intro X0 X1
        first
        | (have j0 := b2e109954 X0 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e109954
      have b2e155930 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
        intro X0 X1
        first
        | (have j0 := b2e155929 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e155929
      have b2e156381 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X0) ∨ (k X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e47167 X0 (M.op X0 X1)
           have i₂ := b2e155930 X0 X1
           grind)
        | exact superpose b2e155930 b2e47167
        | (have j0 := b2e47167 X0 (M.op X0 X1)
           grind)
        | exact resolve b2e47167 b2e155930
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47167 b2e155930
      have b2e156443 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
        intro X0 X1
        first
        | (have j0 := b2e156381 X0 X1
           have j1 := b2e44041 X0 X1 X0
           grind)
        | (have r₁ := b2e156381 x X1
           have r₂ := b2e44041 x X1 x
           grind)
        | exact resolve b2e156381 b2e44041
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e44041 b2e156381
      have b2e157521 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = (τ (M.op (M.op (σ X0) X1) (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e163 X0 (M.op (σ X0) X1)
           have i₂ := b2e156443 (σ X0) X1
           grind)
        | exact superpose b2e156443 b2e163
        | exact resolve b2e163 b2e156443
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e156443
      have b2e160384 : ∀ X0 : G, (k x (τ (M.op (σ x) X0))) = (τ (M.op (M.op (σ x) X0) (σ y))) := by
        intro X0
        first
        | (have i₁ := b2e157521 x X0
           have i₂ := b2e37 (M.op (σ x) X0)
           grind)
        | exact superpose b2e37 b2e157521
        | exact resolve b2e157521 b2e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e37
      have b2e164897 : ∀ X0 : G, (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op y y) = (k (M.op X0 y) x) := by
        intro X0
        first
        | (have i₁ := b2e123242 y x
           have i₂ := b2e37380
           grind)
        | exact superpose b2e37380 b2e123242
        | exact resolve b2e123242 b2e37380
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e37380 b2e123242
      have b2e164899 : ∀ X0 : G, (M.op y y) = (k (M.op X0 y) x) := by
        intro X0
        first
        | (have j0 := b2e164897 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e164897
      have b2e171577 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 (k X1 X2)) := by
        intro X0 X1 X2
        first
        | (have j0 := b2e131603 X1 X2 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e131603
      have b2e171578 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (k X1 X2)) := by
        intro X0 X1 X2
        first
        | (have j0 := b2e171577 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e171577
      have b2e171945 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e171578 X2 (σ X0) (σ X1)
           have i₂ := b2e15 X0 X1
           grind)
        | exact superpose b2e15 b2e171578
        | exact resolve b2e171578 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e172236 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) X2) = (M.op (M.op (k X0 X1) X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e24 (k X0 X1) X2
           have i₂ := b2e171578 (k X0 X1) X0 X1
           grind)
        | exact superpose b2e171578 b2e24
        | exact resolve b2e24 b2e171578
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e173228 : ∀ X0 X1 : G, (M.op X0 (σ (M.op y y))) = (M.op X0 (σ (M.op X1 y))) := by
        intro X0 X1
        first
        | (have i₁ := b2e171945 (M.op X1 y) (M.op y x) X0
           have i₂ := b2e153431 X1
           grind)
        | exact superpose b2e153431 b2e171945
        | exact resolve b2e171945 b2e153431
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e153431
      have b2e173562 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ X0)) = (σ (M.op (k X0 X1) (k X0 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e71 (k X0 X1)
           have i₂ := b2e171945 X0 X1 (σ (k X0 X1))
           grind)
        | exact superpose b2e171945 b2e71
        | exact resolve b2e71 b2e171945
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e171945
      have b2e173696 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ X0)) = (σ (M.op (k X0 X1) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e173562 X0 X1
           have i₂ := b2e171578 (k X0 X1) X0 X1
           grind)
        | exact superpose b2e171578 b2e173562
        | exact resolve b2e173562 b2e171578
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e173562
      have b2e173866 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op X1 y))) := by
        intro X0 X1
        first
        | (have i₁ := b2e173228 X0 X1
           have i₂ := b2e328 y X0
           grind)
        | exact superpose b2e328 b2e173228
        | exact resolve b2e173228 b2e328
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e328 b2e173228
      have b2e174969 : ∀ X0 : G, (M.op (σ (M.op X0 y)) (σ y)) = (σ (M.op (M.op X0 y) (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b2e71 (M.op X0 y)
           have i₂ := b2e173866 (σ (M.op X0 y)) X0
           grind)
        | exact superpose b2e173866 b2e71
        | exact resolve b2e71 b2e173866
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e71 b2e173866
      have b2e175095 : ∀ X0 : G, (σ (M.op (M.op X0 y) y)) = (M.op (σ (M.op X0 y)) (σ y)) := by
        intro X0
        first
        | (have i₁ := b2e174969 X0
           have i₂ := b2e23 y (M.op X0 y) X0
           grind)
        | exact superpose b2e23 b2e174969
        | exact resolve b2e174969 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e174969
      have b2e182286 : ∀ X0 : G, (k (τ (σ (M.op (k y X0) y))) y) = (k (τ (σ (M.op (k y X0) y))) x) := by
        intro X0
        first
        | (have i₁ := b2e79715 (σ (k y x))
           have i₂ := b2e173696 y x
           grind)
        | exact superpose b2e173696 b2e79715
        | exact resolve b2e79715 b2e173696
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e173696
      have b2e182305 : ∀ X0 : G, (k (M.op (k y X0) y) y) = (k (M.op (k y X0) y) x) := by
        intro X0
        first
        | (have i₁ := b2e182286 X0
           have i₂ := b2e11 (M.op (k y X0) y)
           grind)
        | exact superpose b2e11 b2e182286
        | exact resolve b2e182286 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e182286
      have b2e182401 : ∀ X0 : G, (M.op y y) = (k (M.op (k y X0) y) y) := by
        intro X0
        first
        | (have i₁ := b2e182305 X0
           have i₂ := b2e164899 (k y X0)
           grind)
        | exact superpose b2e164899 b2e182305
        | exact resolve b2e182305 b2e164899
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e182305
      have b2e182460 : ∀ X0 : G, (M.op y y) = (M.op (M.op (k y X0) y) y) := by
        intro X0
        first
        | (have i₁ := b2e182401 X0
           have i₂ := b2e8881 (k y X0) y
           grind)
        | exact superpose b2e8881 b2e182401
        | exact resolve b2e182401 b2e8881
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e182401
      have b2e182486 : ∀ X0 : G, (M.op y y) = (M.op (k y X0) y) := by
        intro X0
        first
        | (have i₁ := b2e182460 X0
           have i₂ := b2e172236 y X0 y
           grind)
        | exact superpose b2e172236 b2e182460
        | exact resolve b2e182460 b2e172236
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e182460
      have b2e183266 : ∀ X0 X1 : G, (M.op (M.op y y) X1) = (M.op (k y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e172236 y X0 X1
           have i₂ := b2e182486 X0
           grind)
        | exact superpose b2e182486 b2e172236
        | exact resolve b2e172236 b2e182486
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e172236 b2e182486
      have b2e183501 : ∀ X0 X1 : G, (M.op y X1) = (M.op (k y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e183266 X0 X1
           have i₂ := b2e24 y X1
           grind)
        | exact superpose b2e24 b2e183266
        | exact resolve b2e183266 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e183266
      have b2e185267 : ∀ X0 : G, (M.op (k (σ y) X0) (k (σ y) X0)) = (σ (M.op y (k y (τ X0)))) := by
        intro X0
        first
        | (have i₁ := b2e313 y X0
           have i₂ := b2e183501 (τ X0) (k y (τ X0))
           grind)
        | exact superpose b2e183501 b2e313
        | exact resolve b2e313 b2e183501
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e313 b2e183501
      have b2e185976 : ∀ X0 : G, (σ (M.op y y)) = (M.op (k (σ y) X0) (k (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b2e185267 X0
           have i₂ := b2e171578 y y (τ X0)
           grind)
        | exact superpose b2e171578 b2e185267
        | exact resolve b2e185267 b2e171578
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e185267
      have b2e186191 : ∀ X0 : G, (σ (M.op y y)) = (M.op (k (σ y) X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b2e185976 X0
           have i₂ := b2e171578 (k (σ y) X0) (σ y) X0
           grind)
        | exact superpose b2e171578 b2e185976
        | exact resolve b2e185976 b2e171578
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e185976
      have b2e196220 : (σ (M.op y y)) = (M.op (M.op y y) (σ y)) ∨ (M.op y (σ y)) = (k (σ y) y) := by
        first
        | (have i₁ := b2e186191 x
           have i₂ := b2e150879 (σ y)
           grind)
        | exact superpose b2e150879 b2e186191
        | (have j1 := b2e150879 (σ y)
           grind)
        | exact resolve b2e186191 b2e150879
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e150879 b2e186191
      have b2e196373 : (σ (M.op y y)) = (M.op y (σ y)) ∨ (M.op y (σ y)) = (k (σ y) y) := by
        first
        | (have i₁ := b2e196220
           have i₂ := b2e24 y (σ y)
           grind)
        | exact superpose b2e24 b2e196220
        | exact resolve b2e196220 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e196220
      have b2e196442 : (M.op y (σ y)) = (k (σ y) y) := by
        first
        | (have j1 := b2e1840 y y
           grind)
        | (have r₁ := b2e196373
           have r₂ := b2e1840 y y
           grind)
        | exact resolve b2e196373 b2e1840
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1840 b2e196373
      have b2e196728 : (τ (M.op y (σ y))) = (k y (τ y)) := by
        first
        | (have i₁ := b2e163 y y
           have i₂ := b2e196442
           grind)
        | exact superpose b2e196442 b2e163
        | exact resolve b2e163 b2e196442
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e196442
      have b2e215167 : ∀ X0 : G, (k (τ (σ (M.op (M.op X0 y) y))) y) = (k (τ (σ (M.op (M.op X0 y) y))) x) := by
        intro X0
        first
        | (have i₁ := b2e79715 (σ (M.op X0 y))
           have i₂ := b2e175095 X0
           grind)
        | exact superpose b2e175095 b2e79715
        | exact resolve b2e79715 b2e175095
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e79715 b2e175095
      have b2e215199 : ∀ X0 : G, (k (M.op (M.op X0 y) y) x) = (k (M.op (M.op X0 y) y) y) := by
        intro X0
        first
        | (have i₁ := b2e215167 X0
           have i₂ := b2e11 (M.op (M.op X0 y) y)
           grind)
        | exact superpose b2e11 b2e215167
        | exact resolve b2e215167 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e215167
      have b2e215231 : ∀ X0 : G, (k (M.op (M.op X0 y) y) x) = (M.op (M.op (M.op X0 y) y) y) := by
        intro X0
        first
        | (have i₁ := b2e215199 X0
           have i₂ := b2e8881 (M.op X0 y) y
           grind)
        | exact superpose b2e8881 b2e215199
        | exact resolve b2e215199 b2e8881
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e8881 b2e215199
      have b2e215238 : ∀ X0 : G, (M.op (M.op X0 y) y) = (k (M.op (M.op X0 y) y) x) := by
        intro X0
        first
        | (have i₁ := b2e215231 X0
           have i₂ := b2e32 X0 y y
           grind)
        | exact superpose b2e32 b2e215231
        | exact resolve b2e215231 b2e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e215231
      have b2e215243 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 y) y) := by
        intro X0
        first
        | (have i₁ := b2e215238 X0
           have i₂ := b2e164899 (M.op X0 y)
           grind)
        | exact superpose b2e164899 b2e215238
        | exact resolve b2e215238 b2e164899
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e164899 b2e215238
      have b2e216079 : ∀ X0 X1 : G, (M.op (M.op y y) X1) = (M.op (M.op X0 y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e32 X0 y X1
           have i₂ := b2e215243 X0
           grind)
        | exact superpose b2e215243 b2e32
        | exact resolve b2e32 b2e215243
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e32
      have b2e216109 : ∀ X0 : G, (M.op y y) = (M.op X0 y) ∨ (M.op X0 y) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b2e88 X0 y y
           have i₂ := b2e215243 X0
           grind)
        | exact superpose b2e215243 b2e88
        | (have j0 := b2e88 X0 y x
           grind)
        | exact resolve b2e88 b2e215243
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e88
      have b2e216110 : ∀ X0 : G, (M.op y y) = (M.op X0 y) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b2e253 X0 y y
           have i₂ := b2e215243 X0
           grind)
        | exact superpose b2e215243 b2e253
        | (have j0 := b2e253 X0 y x
           grind)
        | exact resolve b2e253 b2e215243
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e253 b2e215243
      have b2e216394 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have j0 := b2e216110 X0
           have j1 := b2e42010 X0 y
           grind)
        | (have r₁ := b2e216110 y
           have r₂ := b2e42010 y y
           grind)
        | (have r₁ := b2e216110 X0
           have r₂ := b2e42010 X0 y
           grind)
        | exact resolve b2e216110 b2e42010
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e42010 b2e216110
      have b2e216395 : ∀ X0 : G, (M.op X0 y) = (k y X0) := by
        intro X0
        first
        | (have j0 := b2e216109 X0
           have j1 := b2e201 y X0
           grind)
        | (have r₁ := b2e216109 x
           have r₂ := b2e201 y x
           grind)
        | (have r₁ := b2e216109 y
           have r₂ := b2e201 y y
           grind)
        | exact resolve b2e216109 b2e201
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e201 b2e216109
      have b2e216405 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e216079 X0 X1
           have i₂ := b2e24 y X1
           grind)
        | exact superpose b2e24 b2e216079
        | exact resolve b2e216079 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e24 b2e216079
      have b2e216782 : ∀ X0 : G, (τ (M.op y (σ X0))) = (k X0 (τ y)) := by
        intro X0
        first
        | (have i₁ := b2e163 X0 y
           have i₂ := b2e216394 (σ X0)
           grind)
        | exact superpose b2e216394 b2e163
        | exact resolve b2e163 b2e216394
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e163 b2e216394
      have b2e217638 : ∀ X0 : G, (k (τ y) X0) = (τ (M.op (σ X0) y)) := by
        intro X0
        first
        | (have i₁ := b2e153 y X0
           have i₂ := b2e216395 (σ X0)
           grind)
        | exact superpose b2e216395 b2e153
        | exact resolve b2e153 b2e216395
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e153
      have b2e218839 : ∀ X0 : G, (τ (M.op y (σ X0))) = (k X0 (τ (M.op (σ X0) y))) := by
        intro X0
        first
        | (have i₁ := b2e157521 X0 y
           have i₂ := b2e216405 (σ X0) (σ X0)
           grind)
        | exact superpose b2e216405 b2e157521
        | exact resolve b2e157521 b2e216405
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e157521
      have b2e218840 : (τ (M.op y (σ y))) = (k x (τ (M.op (σ x) y))) := by
        first
        | (have i₁ := b2e160384 y
           have i₂ := b2e216405 (σ x) (σ y)
           grind)
        | exact superpose b2e216405 b2e160384
        | exact resolve b2e160384 b2e216405
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e160384 b2e216405
      have b2e219577 : (τ (M.op y (σ y))) = (k x (k (τ y) x)) := by
        first
        | (have i₁ := b2e218840
           have i₂ := b2e217638 x
           grind)
        | exact superpose b2e217638 b2e218840
        | exact resolve b2e218840 b2e217638
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e218840
      have b2e219578 : ∀ X0 : G, (τ (M.op y (σ X0))) = (k X0 (k (τ y) X0)) := by
        intro X0
        first
        | (have i₁ := b2e218839 X0
           have i₂ := b2e217638 X0
           grind)
        | exact superpose b2e217638 b2e218839
        | exact resolve b2e218839 b2e217638
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e217638 b2e218839
      have b2e219729 : (k y (τ y)) = (k x (k (τ y) x)) := by
        first
        | (have i₁ := b2e219577
           have i₂ := b2e196728
           grind)
        | exact superpose b2e196728 b2e219577
        | exact resolve b2e219577 b2e196728
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e196728 b2e219577
      have b2e219730 : ∀ X0 : G, (k X0 (τ y)) = (k X0 (k (τ y) X0)) := by
        intro X0
        first
        | (have i₁ := b2e219578 X0
           have i₂ := b2e216782 X0
           grind)
        | exact superpose b2e216782 b2e219578
        | exact resolve b2e219578 b2e216782
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e216782 b2e219578
      have b2e219734 : (M.op (τ y) y) = (k x (k (τ y) x)) := by
        first
        | (have i₁ := b2e219729
           have i₂ := b2e216395 (τ y)
           grind)
        | exact superpose b2e216395 b2e219729
        | exact resolve b2e219729 b2e216395
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e216395 b2e219729
      have b2e219735 : (k x (τ y)) = (M.op (τ y) y) := by
        first
        | (have i₁ := b2e219734
           have i₂ := b2e219730 x
           grind)
        | exact superpose b2e219730 b2e219734
        | exact resolve b2e219734 b2e219730
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e219730 b2e219734
      have b2e220421 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (τ y) y)) := by
        intro X0
        first
        | (have i₁ := b2e171578 X0 x (τ y)
           have i₂ := b2e219735
           grind)
        | exact superpose b2e219735 b2e171578
        | exact resolve b2e171578 b2e219735
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e171578 b2e219735
      have b2e220444 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b2e220421 X0
           have i₂ := b2e23 y X0 (τ y)
           grind)
        | exact superpose b2e23 b2e220421
        | exact resolve b2e220421 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e23 b2e220421
      have b2e221427 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b2e38664
           have i₂ := b2e220444 y
           grind)
        | exact superpose b2e220444 b2e38664
        | exact resolve b2e38664 b2e220444
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e38664 b2e220444
      have b2e221519 : False := by grind
      exact b2e221519
    · have b3e10 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X2 X1)) := by
        intro X0 X1 X2
        grind
      have b3e13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : (M.op y x) ≠ (M.op y y) := by grind
      have b3e18 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b3e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e15 X0 X0
           have i₂ := b3e53 (σ X0)
           grind)
        | exact superpose b3e53 b3e15
        | exact resolve b3e15 b3e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e63 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b3e62 X0
           have i₂ := b3e53 X0
           grind)
        | exact superpose b3e53 b3e62
        | exact resolve b3e62 b3e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e53 b3e62
      have b3e84 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 X1)) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10 X2 X0 X0
           have i₂ := b3e14 X1 X0
           grind)
        | (have i₁ := b3e10 X0 X0 X1
           have i₂ := b3e14 X0 X1
           grind)
        | exact superpose b3e14 b3e10
        | (have j1 := b3e14 X1 X0
           grind)
        | exact resolve b3e10 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e94 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e84 X0 X1 X2
           have i₂ := b3e10 X2 X1 X0
           grind)
        | exact superpose b3e10 b3e84
        | (have j0 := b3e84 X0 X1 X2
           grind)
        | exact resolve b3e84 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e84
      have b3e262 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (M.op (σ y) X0) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e94 (σ x) X0 (σ y)
           grind)
        | (have i₁ := b3e18
           have i₂ := b3e94 X0 (σ x) (σ y)
           grind)
        | exact superpose b3e94 b3e18
        | (have j1 := b3e94 (σ x) X0 x
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e94 (σ y) (σ x) (σ y)
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e94 (σ x) (σ y) (σ y)
           grind)
        | exact resolve b3e18 b3e94
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e268 : ∀ X0 : G, (M.op (σ y) X0) ≠ (σ (M.op y y)) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b3e262 X0
           have i₂ := b3e63 y
           grind)
        | exact superpose b3e63 b3e262
        | (have j0 := b3e262 X0
           grind)
        | exact resolve b3e262 b3e63
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e262
      have b3e14710 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b3e268 (σ y)
           have i₂ := b3e63 y
           grind)
        | exact superpose b3e63 b3e268
        | (have j0 := b3e268 (σ y)
           grind)
        | (have r₁ := b3e268 (σ y)
           have r₂ := b3e63 y
           grind)
        | exact resolve b3e268 b3e63
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e63 b3e268
      have b3e14721 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
      clear b3e14710
      have b3e14730 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b3e14721
           have i₂ := b3e15 y x
           grind)
        | exact superpose b3e15 b3e14721
        | exact resolve b3e14721 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e14721
      have b3e14746 : (σ (M.op x y)) ≠ (σ (k y x)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e14730
           grind)
        | exact superpose b3e14730 b3e16
        | exact resolve b3e16 b3e14730
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e14730
      have b3e14842 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 x) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b3e14746
           have i₂ := b3e94 x y X0
           grind)
        | exact superpose b3e94 b3e14746
        | (have j1 := b3e94 y x X0
           grind)
        | exact resolve b3e14746 b3e94
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e94 b3e14746
      have b3e14847 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
        intro X0
        first
        | (have j0 := b3e14842 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e14842
      have b3e16592 : (M.op y y) ≠ (M.op y y) := by
        first
        | (have i₁ := b3e17
           have i₂ := b3e14847 y
           grind)
        | exact superpose b3e14847 b3e17
        | (have r₁ := b3e17
           have r₂ := b3e14847 y
           grind)
        | exact resolve b3e17 b3e14847
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e14847
      have b3e16593 : False := by grind
      exact b3e16593
