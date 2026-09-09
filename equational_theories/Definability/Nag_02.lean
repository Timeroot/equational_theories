import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_pyy_pxy_pyx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x x) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e34 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e14 x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x X0
           grind)
        | (have r₁ := b0e14 x x
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e14 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) X0
           grind)
        | (have r₁ := b0e14 (σ x) x
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b0e35 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e37 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
        intro X0
        first
        | (have j0 := b0e34 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e149 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 x X0
           have i₂ := b0e36 (σ X0)
           grind)
        | exact superpose b0e36 b0e17
        | exact resolve b0e17 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e150 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e149 X0
           have i₂ := b0e37 X0
           grind)
        | exact superpose b0e37 b0e149
        | exact resolve b0e149 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e149
      have b0e398 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e150 y
           grind)
        | exact superpose b0e150 b0e18
        | (have r₁ := b0e18
           have r₂ := b0e150 y
           grind)
        | exact resolve b0e18 b0e150
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e150
      have b0e413 : False := by grind
      exact b0e413
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op x x) := by grind
        have b1e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e31 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
          intro X0
          first
          | (have i₁ := b1e12 (M.op X0 X0) X0 x
             have i₂ := b1e12 X0 x (M.op X0 X0)
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e15 x X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 x X0
             grind)
          | (have r₁ := b1e15 x x
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b1e39 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e16 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e45 X0
             have j1 := b1e15 X0 X0
             grind)
          | (have r₁ := b1e45 X0
             have r₂ := b1e15 X0 x
             grind)
          | exact resolve b1e45 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e46 (σ X0)
             grind)
          | exact superpose b1e46 b1e18
          | exact resolve b1e18 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e51 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e48 X0
             have i₂ := b1e46 X0
             grind)
          | exact superpose b1e46 b1e48
          | exact resolve b1e48 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46 b1e48
        have b1e99 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b1e17 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e101 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b1e99 X0 X1
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e99 (k X1 X1) X1
             have r₂ := b1e15 X1 X1
             grind)
          | (have r₁ := b1e99 X0 X1
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e99 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e99
        have b1e160 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
          first
          | (have i₁ := b1e31 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e31
          | exact resolve b1e31 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e167 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ y)) := by
          first
          | (have i₁ := b1e160
             have i₂ := b1e51 x
             grind)
          | exact superpose b1e51 b1e160
          | exact resolve b1e160 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e160
        have b1e170 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e167
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e167
          | exact resolve b1e167 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e167
        have b1e184 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e170
             grind)
          | exact superpose b1e170 b1e19
          | exact resolve b1e19 b1e170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e170
        have b1e190 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b1e101 (M.op X0 X0) X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e101
        have b1e191 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have i₁ := b1e190 X0
             have i₂ := b1e31 X0
             grind)
          | exact superpose b1e31 b1e190
          | exact resolve b1e190 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31 b1e190
        have b1e229 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ y)) := by
          first
          | (have i₁ := b1e191 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e191
          | exact resolve b1e191 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e191
        have b1e234 : (σ (M.op x x)) = (k (σ (M.op x x)) (σ y)) := by
          first
          | (have i₁ := b1e229
             have i₂ := b1e51 x
             grind)
          | exact superpose b1e51 b1e229
          | exact resolve b1e229 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e229
        have b1e239 : (σ (M.op x x)) = (σ (k (M.op x x) y)) := by
          first
          | (have i₁ := b1e234
             have i₂ := b1e18 (M.op x x) y
             grind)
          | exact superpose b1e18 b1e234
          | exact resolve b1e234 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e234
        have b1e240 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e239
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e239
          | exact resolve b1e239 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e239
        have b1e241 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b1e240
             have i₂ := b1e41 y
             grind)
          | exact superpose b1e41 b1e240
          | exact resolve b1e240 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e240
        have b1e242 : False := by grind
        exact b1e242
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e41 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e16 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e41 X0
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e41 X0
             have r₂ := b2e15 X0 x
             grind)
          | exact resolve b2e41 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e42 (σ X0)
             grind)
          | exact superpose b2e42 b2e18
          | exact resolve b2e18 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e47 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e44 X0
             have i₂ := b2e42 X0
             grind)
          | exact superpose b2e42 b2e44
          | exact resolve b2e44 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42 b2e44
        have b2e236 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e47 x
             grind)
          | exact superpose b2e47 b2e21
          | exact resolve b2e21 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47
        have b2e252 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e236
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e236
          | exact resolve b2e236 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e236
        have b2e253 : False := by grind
        exact b2e253
  · rcases eq_or_ne (M.op x x) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e33 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e15 (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ x) X0
             grind)
          | (have r₁ := b3e15 (σ x) x
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e35 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b3e33 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e37 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 x X0
             have i₂ := b3e35 (σ X0)
             grind)
          | exact superpose b3e35 b3e18
          | exact resolve b3e18 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e41 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e16 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e41 X0
             have j1 := b3e15 X0 X0
             grind)
          | (have r₁ := b3e41 X0
             have r₂ := b3e15 X0 x
             grind)
          | exact resolve b3e41 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e181 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e37 x
             grind)
          | exact superpose b3e37 b3e22
          | exact resolve b3e22 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e196 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e181
             have i₂ := b3e42 x
             grind)
          | exact superpose b3e42 b3e181
          | exact resolve b3e181 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42 b3e181
        have b3e226 : (M.op x x) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (M.op x x)
             have i₂ := b3e196
             grind)
          | exact superpose b3e196 b3e13
          | exact resolve b3e13 b3e196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e196
        have b3e227 : x = (M.op x x) := by
          first
          | (have i₁ := b3e226
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e226
          | exact resolve b3e226 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e226
        have b3e233 : False := by grind
        exact b3e233
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ (M.op x x) := by grind
          have b4e22 : (M.op x x) = (M.op y y) := by grind
          have b4e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 (M.op X0 X0) X0 x
               have i₂ := b4e13 X0 x (M.op X0 X0)
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e30 : (M.op x x) = (M.op (M.op x x) y) := by
            first
            | (have i₁ := b4e29 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e29
            | exact resolve b4e29 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29
          have b4e41 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e17 (σ y) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 X0 (σ x)
               grind)
            | (have r₁ := b4e17 (σ x) (σ y)
               have r₂ := b4e24
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k y X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 X0 x
               grind)
            | (have r₁ := b4e17 x y
               have r₂ := b4e22
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e17 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e45 X0
               have j1 := b4e16 X0 X0
               grind)
            | (have r₁ := b4e45 X0
               have r₂ := b4e16 X0 x
               grind)
            | exact resolve b4e45 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e46 (σ X0)
               grind)
            | exact superpose b4e46 b4e19
            | exact resolve b4e19 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e51 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e48 X0
               have i₂ := b4e46 X0
               grind)
            | exact superpose b4e46 b4e48
            | exact resolve b4e48 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46 b4e48
          have b4e1065 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
            first
            | (have j0 := b4e42 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e4268 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b4e41 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e4270 : (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e4268
               have i₂ := b4e51 x
               grind)
            | exact superpose b4e51 b4e4268
            | exact resolve b4e4268 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51 b4e4268
          have b4e4297 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e4270
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e4270
            | exact resolve b4e4270 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4270
          have b4e9516 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e4297
               grind)
            | exact superpose b4e4297 b4e20
            | exact resolve b4e20 b4e4297
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4297
          have b4e15562 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b4e9516
               have i₂ := b4e1065
               grind)
            | exact superpose b4e1065 b4e9516
            | exact resolve b4e9516 b4e1065
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1065 b4e9516
          have b4e15587 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
          clear b4e15562
          have b4e15796 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b4e14 (M.op x x)
               have i₂ := b4e15587
               grind)
            | exact superpose b4e15587 b4e14
            | exact resolve b4e14 b4e15587
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15587
          have b4e15837 : y = (M.op x x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b4e15796
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e15796
            | exact resolve b4e15796 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15796
          have b4e15838 : y = (M.op x x) := by grind
          clear b4e15837
          have b4e16110 : y = (M.op y y) := by
            first
            | (have i₁ := b4e30
               have i₂ := b4e15838
               grind)
            | exact superpose b4e15838 b4e30
            | exact resolve b4e30 b4e15838
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30
          have b4e16159 : ∀ X0 X1 : G, x = (M.op x (M.op X0 (M.op X1 y))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 x X0 X1
               have i₂ := b4e15838
               grind)
            | exact superpose b4e15838 b4e13
            | exact resolve b4e13 b4e15838
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15838
          have b4e20736 : ∀ X0 : G, x = (M.op x (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e16159 X0 y
               have i₂ := b4e16110
               grind)
            | exact superpose b4e16110 b4e16159
            | exact resolve b4e16159 b4e16110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16110
          have b4e22629 : x = (M.op x x) := by
            first
            | (have i₁ := b4e16159 x x
               have i₂ := b4e20736 x
               grind)
            | exact superpose b4e20736 b4e16159
            | exact resolve b4e16159 b4e20736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16159 b4e20736
          have b4e22651 : False := by grind
          exact b4e22651
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : (M.op x x) = (M.op y y) := by grind
          have b5e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e40 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e17 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e40 X0
               have j1 := b5e16 X0 X0
               grind)
            | (have r₁ := b5e40 X0
               have r₂ := b5e16 X0 x
               grind)
            | exact resolve b5e40 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e43 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e41 (σ X0)
               grind)
            | exact superpose b5e41 b5e19
            | exact resolve b5e19 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e43 X0
               have i₂ := b5e41 X0
               grind)
            | exact superpose b5e41 b5e43
            | exact resolve b5e43 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e43
          have b5e199 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e46 y
               grind)
            | exact superpose b5e46 b5e24
            | exact resolve b5e24 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e209 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e199
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e199
            | exact resolve b5e199 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e199
          have b5e213 : False := by grind
          exact b5e213
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e31 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e15 (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ x) X0
             grind)
          | (have r₁ := b6e15 (σ x) x
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e32 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b6e31 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e34 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e32 (σ X0)
             grind)
          | exact superpose b6e32 b6e18
          | exact resolve b6e18 b6e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e36 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e16 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e37 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e36 X0
             have j1 := b6e15 X0 X0
             grind)
          | (have r₁ := b6e36 X0
             have r₂ := b6e15 X0 x
             grind)
          | exact resolve b6e36 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e150 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e34 x
             grind)
          | exact superpose b6e34 b6e22
          | exact resolve b6e22 b6e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e165 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e150
             have i₂ := b6e37 x
             grind)
          | exact superpose b6e37 b6e150
          | exact resolve b6e150 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37 b6e150
        have b6e195 : (M.op x x) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (M.op x x)
             have i₂ := b6e165
             grind)
          | exact superpose b6e165 b6e13
          | exact resolve b6e13 b6e165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e165
        have b6e196 : x = (M.op x x) := by
          first
          | (have i₁ := b6e195
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e195
          | exact resolve b6e195 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e195
        have b6e202 : False := by grind
        exact b6e202
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : (M.op x x) ≠ (M.op y y) := by grind
          have b7e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e48 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e17 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e48 X0
               have j1 := b7e16 X0 X0
               grind)
            | (have r₁ := b7e48 X0
               have r₂ := b7e16 X0 x
               grind)
            | exact resolve b7e48 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e51 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e49 (σ X0)
               grind)
            | exact superpose b7e49 b7e19
            | exact resolve b7e19 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e51 X0
               have i₂ := b7e49 X0
               grind)
            | exact superpose b7e49 b7e51
            | exact resolve b7e51 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49 b7e51
          have b7e276 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e56 y
               grind)
            | exact superpose b7e56 b7e24
            | exact resolve b7e24 b7e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e294 : (σ (M.op x x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e276
               have i₂ := b7e56 x
               grind)
            | exact superpose b7e56 b7e276
            | exact resolve b7e276 b7e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56 b7e276
          have b7e355 : (M.op y y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e294
               grind)
            | exact superpose b7e294 b7e14
            | exact resolve b7e14 b7e294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e294
          have b7e356 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b7e355
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e355
            | exact resolve b7e355 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e355
          have b7e364 : False := by grind
          exact b7e364
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : (M.op x x) ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e43 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e17 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e43 X0
               have j1 := b8e16 X0 X0
               grind)
            | (have r₁ := b8e43 X0
               have r₂ := b8e16 X0 x
               grind)
            | exact resolve b8e43 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e44 (σ X0)
               grind)
            | exact superpose b8e44 b8e19
            | exact resolve b8e19 b8e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e51 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e46 X0
               have i₂ := b8e44 X0
               grind)
            | exact superpose b8e44 b8e46
            | exact resolve b8e46 b8e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44 b8e46
          have b8e90 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 X0) = X0 ∨ (k X0 y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b8e22
               have i₂ := b8e18 X0 y
               grind)
            | (have i₁ := b8e22
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e22
            | (have j1 := b8e18 X0 y
               grind)
            | (have r₁ := b8e22
               have r₂ := b8e18 x y
               grind)
            | (have r₁ := b8e22
               have r₂ := b8e18 y x
               grind)
            | exact resolve b8e22 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
          have b8e98 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e91 X0 X1
               have i₂ := b8e51 X0
               grind)
            | exact superpose b8e51 b8e91
            | (have j0 := b8e91 X0 X1
               grind)
            | exact resolve b8e91 b8e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91
          have b8e99 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b8e90 X0
               have j1 := b8e16 X0 y
               grind)
            | (have r₁ := b8e90 X0
               have r₂ := b8e16 X0 x
               grind)
            | exact resolve b8e90 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90
          have b8e129 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e98 X0 X1
               have i₂ := b8e51 X1
               grind)
            | exact superpose b8e51 b8e98
            | (have j0 := b8e98 X0 X1
               grind)
            | exact resolve b8e98 b8e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98
          have b8e141 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e129 X0 X1
               have i₂ := b8e51 X0
               grind)
            | exact superpose b8e51 b8e129
            | (have j0 := b8e129 X0 X1
               grind)
            | exact resolve b8e129 b8e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e129
          have b8e204 : (M.op x y) = (k x y) := by
            first
            | (have j0 := b8e99 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99
          have b8e246 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e51 x
               grind)
            | exact superpose b8e51 b8e23
            | exact resolve b8e23 b8e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e247 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e51 y
               grind)
            | exact superpose b8e51 b8e24
            | exact resolve b8e24 b8e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e265 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e247
               have i₂ := b8e51 x
               grind)
            | exact superpose b8e51 b8e247
            | exact resolve b8e247 b8e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e51 b8e247
          have b8e3821 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e141 x y
               grind)
            | exact superpose b8e141 b8e20
            | (have j1 := b8e141 x y
               grind)
            | exact resolve b8e20 b8e141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e141
          have b8e3835 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e3821
               have r₂ := b8e265
               grind)
            | exact resolve b8e3821 b8e265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e265 b8e3821
          have b8e3889 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e3835
               have r₂ := b8e246
               grind)
            | exact resolve b8e3835 b8e246
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e246 b8e3835
          have b8e3902 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e3889
               have i₂ := b8e204
               grind)
            | exact superpose b8e204 b8e3889
            | exact resolve b8e3889 b8e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e204 b8e3889
          have b8e3903 : False := by grind
          exact b8e3903

/-- `Equation4478`: `x ◇ (y ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_x_pyx_pxy_Equation4478 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4478 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4478.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
        intro X0 X1 X2 X3
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
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y x) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b0e34 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X2 X4) X5) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
        intro X0 X1 X2 X4 X5
        first
        | (have i₁ := b0e11 X2 (M.op X0 x) X4 X5
           have i₂ := b0e11 X0 X1 x (M.op X0 x)
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
        intro X0 X1 X2 X4 X5
        first
        | (have i₁ := b0e11 X0 x X4 X5
           have i₂ := b0e11 X0 x X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ y) X0 (σ x) X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 y X0 x X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X1 x x
           have i₂ := b0e11 X0 X2 x x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 X0 X4 X1 (M.op x x)
           have i₂ := b0e11 (M.op X0 X1) x X2 X3
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ X0 ∨ (M.op X3 X3) = (k (M.op X3 X3) X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e14 (M.op X3 X3) X0
           have i₂ := b0e11 X0 X3 X1 X2
           grind)
        | exact superpose b0e11 b0e14
        | (have j0 := b0e14 (M.op X3 X3) X0
           grind)
        | (have r₁ := b0e14 X3 (M.op X0 (M.op X1 X1))
           have r₂ := b0e11 X0 X1 (M.op X1 X1) X3
           grind)
        | exact resolve b0e14 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
        intro X0 X2
        first
        | (have i₁ := b0e40 x X2
           have i₂ := b0e40 x X0
           grind)
        | (have i₁ := b0e40 X0 x
           have i₂ := b0e40 X0 (M.op X0 X0)
           grind)
        | exact superpose b0e40 b0e40
        | exact resolve b0e40 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
      have b0e67 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op X1 (M.op X2 X2)) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 X2 X1 X3
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e11 X0 X1 X2 X3
           have i₂ := b0e16 (M.op X0 X2) X1
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 X1
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e71 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (k X0 (M.op X1 X1)) ∨ (M.op (M.op (M.op X1 X1) X2) X3) = X0 ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X1 X1) X1 X2 X3
           have i₂ := b0e16 X0 (M.op X1 X1)
           grind)
        | (have i₁ := b0e11 X0 X1 X2 X3
           have i₂ := b0e16 (M.op X0 (M.op X1 X1)) X1
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 (M.op X1 X1)
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e92 : ∀ X0 : G, y = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e19
           have i₂ := b0e47 x X0
           grind)
        | (have i₁ := b0e19
           have i₂ := b0e47 X0 x
           grind)
        | exact superpose b0e47 b0e19
        | exact resolve b0e19 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e100 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e104 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e100 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e100
      have b0e129 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k X0 (τ X1))
           have i₂ := b0e28 X1 X0
           grind)
        | exact superpose b0e28 b0e12
        | exact resolve b0e12 b0e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e182 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X0 X3) ∨ (k X4 (M.op X0 X3)) = X4 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e14 X4 (M.op X0 X3)
           have i₂ := b0e35 X0 X3 X4 X1 X2
           grind)
        | (have i₁ := b0e14 X4 (M.op X0 X3)
           have i₂ := b0e35 X0 X1 X2 X3 X4
           grind)
        | exact superpose b0e35 b0e14
        | (have j0 := b0e14 X4 (M.op X0 X3)
           grind)
        | exact resolve b0e14 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e184 : ∀ X0 X1 X2 X3 X4 : G, (k X4 (M.op X0 X3)) = (M.op X4 (M.op X0 X3)) ∨ (M.op (M.op X0 X1) X2) = X4 ∨ (M.op X0 X3) = (M.op (M.op X0 X3) X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e16 X4 (M.op X0 X3)
           have i₂ := b0e35 X0 X3 (M.op X0 X3) X1 X2
           grind)
        | (have i₁ := b0e16 X4 (M.op X0 X3)
           have i₂ := b0e35 X0 X1 X2 X3 (M.op X0 X3)
           grind)
        | exact superpose b0e35 b0e16
        | (have j0 := b0e16 X4 (M.op X0 X3)
           grind)
        | exact resolve b0e16 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e204 : ∀ X0 X2 : G, (M.op (σ y) X0) = (M.op (σ y) X2) := by
        intro X0 X2
        first
        | (have i₁ := b0e39 x X2
           have i₂ := b0e39 x X0
           grind)
        | (have i₁ := b0e39 X0 x
           have i₂ := b0e39 X0 (M.op X0 X0)
           grind)
        | exact superpose b0e39 b0e39
        | exact resolve b0e39 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e258 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X1))) = (M.op X2 (M.op X3 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e41 X2 X3 (M.op X0 x)
           have i₂ := b0e11 X0 X1 x (M.op X0 x)
           grind)
        | exact superpose b0e11 b0e41
        | exact resolve b0e41 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e259 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e41 X0 X1 y
           have i₂ := b0e92 y
           grind)
        | exact superpose b0e92 b0e41
        | exact resolve b0e41 b0e92
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e318 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X1))) = (M.op X2 y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e258 X0 X1 X2 x
           have i₂ := b0e259 X2 x
           grind)
        | exact superpose b0e259 b0e258
        | exact resolve b0e258 b0e259
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e258
      have b0e334 : ∀ X0 X2 : G, (M.op X2 y) = (M.op X2 (M.op X0 y)) := by
        intro X0 X2
        first
        | (have i₁ := b0e318 X0 x X2
           have i₂ := b0e259 X0 x
           grind)
        | exact superpose b0e259 b0e318
        | exact resolve b0e318 b0e259
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e318
      have b0e403 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e34 y x X0 X1 X2
           have i₂ := b0e92 (M.op x x)
           grind)
        | exact superpose b0e92 b0e34
        | exact resolve b0e34 b0e92
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e92
      have b0e432 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 (M.op X2 X2)))) = (k (M.op X0 (M.op X1 (M.op X2 X2))) (M.op X0 X3)) ∨ (M.op X0 X3) = (M.op (M.op X0 X3) (M.op X0 (M.op X1 (M.op X2 X2)))) := by
        intro X0 X1 X2 X3
        grind
      have b0e471 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 y))) = (k (M.op X0 (M.op X1 y)) (M.op X0 X3)) ∨ (M.op X0 X3) = (M.op (M.op X0 X3) (M.op X0 (M.op X1 (M.op X2 X2)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e432 X0 X0 X1 X3
           have i₂ := b0e259 X0 X1
           grind)
        | exact superpose b0e259 b0e432
        | (have j0 := b0e432 X0 X1 X2 X3
           grind)
        | exact resolve b0e432 b0e259
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e432
      have b0e507 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op X0 y)) = (k (M.op X0 y) (M.op X0 X3)) ∨ (M.op X0 X3) = (M.op (M.op X0 X3) (M.op X0 (M.op X1 (M.op X2 X2)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e471 X2 X0 X2 X3
           have i₂ := b0e334 X0 X2
           grind)
        | exact superpose b0e334 b0e471
        | (have j0 := b0e471 X0 X1 X2 X3
           grind)
        | exact resolve b0e471 b0e334
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e471
      have b0e535 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 y) (M.op X0 X3)) = (M.op (M.op X0 X3) y) ∨ (M.op X0 X3) = (M.op (M.op X0 X3) (M.op X0 (M.op X1 (M.op X2 X2)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e507 X0 X1 X2 X3
           have i₂ := b0e334 X0 (M.op X0 X3)
           grind)
        | exact superpose b0e334 b0e507
        | (have j0 := b0e507 X0 X1 X2 X3
           grind)
        | exact resolve b0e507 b0e334
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e334 b0e507
      have b0e548 : ∀ X0 X1 X2 X3 : G, (M.op X0 y) = (k (M.op X0 y) (M.op X0 X3)) ∨ (M.op X0 X3) = (M.op (M.op X0 X3) (M.op X0 (M.op X1 (M.op X2 X2)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e535 X0 X1 X2 X3
           have i₂ := b0e403 X0 X3 y
           grind)
        | exact superpose b0e403 b0e535
        | (have j0 := b0e535 X0 X1 X2 X3
           grind)
        | exact resolve b0e535 b0e403
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e535
      have b0e550 : ∀ X0 X3 : G, (M.op X0 y) = (k (M.op X0 y) (M.op X0 X3)) := by
        intro X0 X3
        first
        | (have j0 := b0e548 X0 x x X3
           have j1 := b0e182 X0 x x X3 (M.op X0 y)
           grind)
        | (have r₁ := b0e548 X0 x x x
           have r₂ := b0e182 X0 x (M.op X0 (M.op x (M.op x x))) x x
           grind)
        | exact resolve b0e548 b0e182
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e548
      have b0e754 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op (M.op X0 X2) X3) ∨ (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e14 X4 (M.op (M.op X0 X2) X3)
           have i₂ := b0e42 X0 X2 X3 X4 X1
           grind)
        | exact superpose b0e42 b0e14
        | (have j0 := b0e14 X4 (M.op (M.op X0 X2) X3)
           grind)
        | exact resolve b0e14 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e773 : ∀ X0 X2 X3 X4 : G, (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
        intro X0 X2 X3 X4
        first
        | (have j0 := b0e754 X0 x X2 X3 X4
           grind)
        | (have r₁ := b0e754 X0 x X2 X3 X4
           have r₂ := b0e11 X0 x X2 X3
           grind)
        | exact resolve b0e754 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e754
      have b0e838 : ∀ X0 X4 : G, (k X4 (M.op X0 y)) = X4 := by
        intro X0 X4
        first
        | (have i₁ := b0e773 X0 x x X4
           have i₂ := b0e403 X0 x x
           grind)
        | exact superpose b0e403 b0e773
        | exact resolve b0e773 b0e403
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e773
      have b0e1457 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e20
           have i₂ := b0e204 (σ x) X0
           grind)
        | (have i₁ := b0e20
           have i₂ := b0e204 X0 (σ x)
           grind)
        | exact superpose b0e204 b0e20
        | exact resolve b0e20 b0e204
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e204
      have b0e1609 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (σ y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e34 (σ y) x X0 X1 X2
           have i₂ := b0e1457 (M.op x x)
           grind)
        | exact superpose b0e1457 b0e34
        | exact resolve b0e34 b0e1457
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34 b0e1457
      have b0e1621 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e1609 X0 x x
           have i₂ := b0e403 X0 x x
           grind)
        | exact superpose b0e403 b0e1609
        | exact resolve b0e1609 b0e403
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1609
      have b0e1851 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e104 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1852 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e104 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e104
      have b0e1911 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e1621 (σ x)
           grind)
        | exact superpose b0e1621 b0e18
        | exact resolve b0e18 b0e1621
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1621
      have b0e2065 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X3) = (k X1 X3) ∨ (M.op X1 X2) = (M.op X3 X0) ∨ (M.op X0 X4) = (k X0 X4) ∨ (M.op X3 X1) = X3 ∨ (M.op X4 X0) = X4 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e67 X1 X3 X4 X2
           have i₂ := b0e16 X0 X4
           grind)
        | (have i₁ := b0e67 X0 X1 X2 X3
           have i₂ := b0e16 (M.op X2 X2) X1
           grind)
        | exact superpose b0e16 b0e67
        | (have j0 := b0e67 X1 X3 X2 X3
           have j1 := b0e16 X1 X3
           grind)
        | exact resolve b0e67 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2091 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X4) = (k X2 X4) ∨ (M.op X0 X4) = (k X0 X4) ∨ (M.op X0 X1) = (M.op X2 X3) ∨ (M.op X4 X2) = X4 ∨ (M.op X4 X0) = X4 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e67 X0 X4 x X1
           have i₂ := b0e67 X2 X4 x X3
           grind)
        | (have i₁ := b0e67 X0 X0 X2 X3
           have i₂ := b0e67 X0 X1 X2 (M.op X2 X2)
           grind)
        | exact superpose b0e67 b0e67
        | (have j0 := b0e67 X2 X4 X2 X3
           have j1 := b0e67 X2 X4 X2 X3
           grind)
        | exact resolve b0e67 b0e67
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2266 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e67 X0 X0 x x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67
      have b0e2272 : ∀ X0 : G, (M.op X0 y) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e2266 X0 x
           have i₂ := b0e259 X0 x
           grind)
        | exact superpose b0e259 b0e2266
        | (have j0 := b0e2266 X0 x
           grind)
        | exact resolve b0e2266 b0e259
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2266
      have b0e3326 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e64 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e64
      have b0e3327 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e3326 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3326
      have b0e4138 : ∀ X0 X1 X4 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X4 X4) = (k (M.op X4 X4) (M.op X1 X1)) ∨ (M.op X0 (M.op X1 X1)) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1 X4
        first
        | (have i₁ := b0e43 (M.op X1 X1) x x X4
           have i₂ := b0e71 X0 X1 x x
           grind)
        | (have i₁ := b0e43 X0 X1 x x
           have i₂ := b0e71 (M.op (M.op X0 X1) x) X1 x x
           grind)
        | exact superpose b0e71 b0e43
        | (have j0 := b0e43 (M.op X1 X1) X1 x X4
           have j1 := b0e71 X0 X1 x x
           grind)
        | (have r₁ := b0e43 (M.op X1 X1) x x x
           have r₂ := b0e71 (M.op X1 X1) X1 x x
           grind)
        | (have r₁ := b0e43 (M.op (M.op (M.op X1 X1) x) x) X1 x x
           have r₂ := b0e71 (M.op (M.op (M.op (M.op (M.op X1 X1) x) x) X1) x) X1 x x
           grind)
        | exact resolve b0e43 b0e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e71
      have b0e4221 : ∀ X0 X1 X4 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X4 X4) = (k (M.op X4 X4) (M.op X1 X1)) ∨ (M.op X0 (M.op X1 X1)) = (k X0 (M.op X1 X1)) := by
        intro X0 X1 X4
        first
        | (have j0 := b0e4138 X0 X1 X4
           have j1 := b0e182 X1 X1 x X1 (M.op X4 X4)
           grind)
        | (have r₁ := b0e4138 (k (M.op X1 X1) (M.op X0 x)) X1 X4
           have r₂ := b0e182 X0 X1 x x (M.op X1 X1)
           grind)
        | (have r₁ := b0e4138 x X1 X4
           have r₂ := b0e182 X1 X1 x X1 X4
           grind)
        | exact resolve b0e4138 b0e182
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e182 b0e4138
      have b0e4263 : ∀ X0 X1 X4 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 (M.op X1 X1)) = (M.op X0 y) ∨ (M.op X4 X4) = (k (M.op X4 X4) (M.op X1 X1)) := by
        intro X0 X1 X4
        first
        | (have i₁ := b0e4221 X0 X1 X4
           have i₂ := b0e259 X0 X1
           grind)
        | exact superpose b0e259 b0e4221
        | (have j0 := b0e4221 X0 X1 X4
           grind)
        | (have r₁ := b0e4221 (M.op (M.op X1 X1) y) (M.op X1 X1) X4
           have r₂ := b0e259 (M.op X1 X1) X1
           grind)
        | (have r₁ := b0e4221 (M.op y (M.op X1 X1)) y X4
           have r₂ := b0e259 y X1
           grind)
        | exact resolve b0e4221 b0e259
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4221
      have b0e4850 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e129 X0 (M.op X1 y)
           have i₂ := b0e838 X1 (σ X0)
           grind)
        | exact superpose b0e838 b0e129
        | exact resolve b0e129 b0e838
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e838
      have b0e4880 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 y))) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e4850 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e4850
        | exact resolve b0e4850 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4850
      have b0e5641 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 y)))) := by
        intro X0 X1
        first
        | (have i₁ := b0e129 X0 (τ (M.op X1 y))
           have i₂ := b0e4880 (σ X0) X1
           grind)
        | exact superpose b0e4880 b0e129
        | exact resolve b0e129 b0e4880
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e129
      have b0e5644 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 y)))) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e5641 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e5641
        | exact resolve b0e5641 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5641
      have b0e9661 : ∀ X0 : G, (σ (τ (τ (M.op X0 y)))) ≠ (σ (τ (τ (M.op X0 y)))) ∨ (σ (τ (τ (M.op X0 y)))) = (M.op (σ (τ (τ (M.op X0 y)))) (σ (τ (τ (M.op X0 y))))) := by
        intro X0
        first
        | (have i₁ := b0e3327 (τ (τ (M.op X0 y)))
           have i₂ := b0e5644 (τ (τ (M.op X0 y))) X0
           grind)
        | exact superpose b0e5644 b0e3327
        | (have j0 := b0e3327 (τ (τ (M.op X0 y)))
           grind)
        | exact resolve b0e3327 b0e5644
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5644
      have b0e9665 : ∀ X0 : G, (σ (M.op X0 y)) ≠ (σ (M.op X0 y)) ∨ (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b0e3327 (M.op X0 y)
           have i₂ := b0e550 X0 y
           grind)
        | exact superpose b0e550 b0e3327
        | (have j0 := b0e3327 (M.op X0 y)
           grind)
        | exact resolve b0e3327 b0e550
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e550
      have b0e9673 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) := by
        intro X0
        first
        | (have j0 := b0e9665 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9665
      have b0e9676 : ∀ X0 : G, (σ (τ (τ (M.op X0 y)))) = (M.op (σ (τ (τ (M.op X0 y)))) (σ (τ (τ (M.op X0 y))))) := by
        intro X0
        first
        | (have j0 := b0e9661 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9661
      have b0e9703 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (τ (M.op X0 y)) (τ (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b0e9676 X0
           have i₂ := b0e13 (τ (M.op X0 y))
           grind)
        | exact superpose b0e13 b0e9676
        | exact resolve b0e9676 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9676
      have b0e10743 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X0 X3) ∨ (M.op (M.op X0 X3) (M.op X0 X3)) = (k (M.op X0 X3) (M.op X0 X3)) ∨ (M.op X0 X3) = (M.op (M.op X0 X3) (M.op X0 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e2272 (M.op X0 X3)
           have i₂ := b0e35 X0 X3 y X1 X2
           grind)
        | (have i₁ := b0e2272 (M.op X0 X3)
           have i₂ := b0e35 X0 X1 X2 X3 y
           grind)
        | exact superpose b0e35 b0e2272
        | (have j0 := b0e2272 (M.op X0 X3)
           grind)
        | exact resolve b0e2272 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e2272
      have b0e10770 : ∀ X0 X3 : G, (M.op (M.op X0 X3) (M.op X0 X3)) = (k (M.op X0 X3) (M.op X0 X3)) ∨ (M.op X0 X3) = (M.op (M.op X0 X3) (M.op X0 X3)) := by
        intro X0 X3
        first
        | (have j0 := b0e10743 X0 x x X3
           have j1 := b0e184 X0 X3 (M.op X0 X3) X3 (M.op X0 X3)
           grind)
        | (have r₁ := b0e10743 X0 x x X3
           have r₂ := b0e184 X0 x x X3 (M.op X0 X3)
           grind)
        | (have r₁ := b0e10743 (M.op X0 x) x x x
           have r₂ := b0e184 X0 x x X3 (M.op (M.op (M.op X0 x) x) x)
           grind)
        | (have r₁ := b0e10743 X0 X3 x X3
           have r₂ := b0e184 X0 x x X3 x
           grind)
        | exact resolve b0e10743 b0e184
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e184 b0e10743
      have b0e10780 : ∀ X0 X3 : G, (M.op X0 y) = (k (M.op X0 X3) (M.op X0 X3)) ∨ (M.op X0 X3) = (M.op (M.op X0 X3) (M.op X0 X3)) := by
        intro X0 X3
        first
        | (have i₁ := b0e10770 X0 X3
           have i₂ := b0e403 X0 X3 (M.op X0 X3)
           grind)
        | exact superpose b0e403 b0e10770
        | (have j0 := b0e10770 X0 X3
           grind)
        | exact resolve b0e10770 b0e403
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10770
      have b0e10788 : ∀ X0 X3 : G, (M.op X0 y) = (k (M.op X0 X3) (M.op X0 X3)) ∨ (M.op X0 X3) = (M.op X0 y) := by
        intro X0 X3
        first
        | (have i₁ := b0e10780 X0 X3
           have i₂ := b0e403 X0 X3 (M.op X0 X3)
           grind)
        | exact superpose b0e403 b0e10780
        | (have j0 := b0e10780 X0 X3
           grind)
        | exact resolve b0e10780 b0e403
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10780
      have b0e12531 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e1851 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1851
      have b0e26787 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e4263 (M.op X0 X0) X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4263
      have b0e26789 : ∀ X0 X1 : G, (M.op X0 y) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e26787 X0 X1
           have i₂ := b0e403 X0 X0 y
           grind)
        | exact superpose b0e403 b0e26787
        | (have j0 := b0e26787 X0 X1
           grind)
        | exact resolve b0e26787 b0e403
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26787
      have b0e31905 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ (M.op X0 y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e259 X1 (σ (M.op X0 y))
           have i₂ := b0e9673 X0
           grind)
        | exact superpose b0e9673 b0e259
        | exact resolve b0e259 b0e9673
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33298 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) y) := by
        intro X0
        first
        | (have i₁ := b0e9673 X0
           have i₂ := b0e31905 X0 (σ (M.op X0 y))
           grind)
        | exact superpose b0e31905 b0e9673
        | exact resolve b0e9673 b0e31905
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9673 b0e31905
      have b0e35431 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e403 (σ (M.op X0 y)) y x
           have i₂ := b0e33298 X0
           grind)
        | exact superpose b0e33298 b0e403
        | exact resolve b0e403 b0e33298
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33298
      have b0e50590 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (τ (M.op X0 y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e259 X1 (τ (M.op X0 y))
           have i₂ := b0e9703 X0
           grind)
        | exact superpose b0e9703 b0e259
        | exact resolve b0e259 b0e9703
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e50630 : ∀ X0 X1 : G, (M.op (τ (M.op X0 y)) X1) = (M.op (τ (M.op X0 y)) y) := by
        intro X0 X1
        first
        | (have i₁ := b0e403 (τ (M.op X0 y)) (τ (M.op X0 y)) X1
           have i₂ := b0e9703 X0
           grind)
        | exact superpose b0e9703 b0e403
        | exact resolve b0e403 b0e9703
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51166 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (τ (M.op X0 y)) y) := by
        intro X0
        first
        | (have i₁ := b0e9703 X0
           have i₂ := b0e50590 X0 (τ (M.op X0 y))
           grind)
        | exact superpose b0e50590 b0e9703
        | exact resolve b0e9703 b0e50590
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9703 b0e50590
      have b0e52152 : ∀ X0 X1 : G, (τ (M.op X0 y)) = (M.op (τ (M.op X0 y)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e403 (τ (M.op X0 y)) y x
           have i₂ := b0e51166 X0
           grind)
        | exact superpose b0e51166 b0e403
        | exact resolve b0e403 b0e51166
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51166
      have b0e53828 : ∀ X0 X1 : G, (τ (τ (M.op X0 y))) = (M.op (τ (τ (M.op X0 y))) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e52152 (τ (M.op X0 y)) X1
           have i₂ := b0e52152 X0 y
           grind)
        | exact superpose b0e52152 b0e52152
        | exact resolve b0e52152 b0e52152
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e59144 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X2) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e2065 X0 X0 X2 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2065
      have b0e59145 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X2) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e59144 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59144
      have b0e59146 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X2) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e59145 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59145
      have b0e61457 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X2) = (M.op X0 X3) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e2091 X0 X2 X0 X3 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2091
      have b0e61462 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X2) = (M.op X0 X3) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e61457 X0 X1 X2 X3
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61457
      have b0e61463 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X2) = (M.op X0 X3) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e61462 X0 X1 X2 X3
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61462
      have b0e161294 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 X1) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X2 X0) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1852 X2 X0
           have i₂ := b0e59146 X0 X1 X2
           grind)
        | (have i₁ := b0e1852 X0 X1
           have i₂ := b0e59146 X0 X1 X2
           grind)
        | exact superpose b0e59146 b0e1852
        | (have j0 := b0e1852 X0 X2
           have j1 := b0e59146 X0 X2 X2
           grind)
        | (have r₁ := b0e1852 X1 X0
           have r₂ := b0e59146 X0 X1 X1
           grind)
        | (have r₁ := b0e1852 X0 X2
           have r₂ := b0e59146 X0 X2 X2
           grind)
        | exact resolve b0e1852 b0e59146
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1852
      have b0e161517 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e59146 X1 X0 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59146
      have b0e161518 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 X1) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = X2 ∨ (M.op X2 X0) = X2 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e161294 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e161294
      have b0e161582 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 X1) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X2 X0) = X2 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e161518 X0 X1 X2
           have j1 := b0e161517 X2 X0 X2
           grind)
        | (have r₁ := b0e161518 X1 X1 X2
           have r₂ := b0e161517 (k X1 X2) X1 X2
           grind)
        | (have r₁ := b0e161518 X1 X2 X0
           have r₂ := b0e161517 X0 X1 X2
           grind)
        | (have r₁ := b0e161518 X0 X1 (M.op X1 X2)
           have r₂ := b0e161517 (M.op X0 X1) X1 X2
           grind)
        | exact resolve b0e161518 b0e161517
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e161517 b0e161518
      have b0e161813 : ∀ X0 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X2 X0) = X2 := by
        intro X0 X2
        first
        | (have j0 := b0e161582 X0 x X2
           have j1 := b0e61463 X0 X2 X2 x
           grind)
        | (have r₁ := b0e161582 X0 x X2
           have r₂ := b0e61463 X0 x X2 x
           grind)
        | (have r₁ := b0e161582 X0 X2 x
           have r₂ := b0e61463 X0 x X2 x
           grind)
        | exact resolve b0e161582 b0e61463
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61463 b0e161582
      have b0e162225 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X0 X1
           have i₂ := b0e161813 (σ X0) (σ X1)
           grind)
        | exact superpose b0e161813 b0e17
        | (have j1 := b0e161813 (σ X0) (σ X1)
           grind)
        | exact resolve b0e17 b0e161813
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e161813
      have b0e182968 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k (M.op X0 X0) (M.op X0 X0)) := by
        intro X0
        first
        | (have j0 := b0e26789 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26789
      have b0e182971 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 X0) (M.op X0 X0)) := by
        intro X0
        first
        | (have j0 := b0e182968 X0
           have j1 := b0e10788 X0 X0
           grind)
        | (have r₁ := b0e182968 x
           have r₂ := b0e10788 x x
           grind)
        | (have r₁ := b0e182968 y
           have r₂ := b0e10788 y y
           grind)
        | exact resolve b0e182968 b0e10788
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10788 b0e182968
      have b0e210063 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (σ X1) (σ X0)
           have i₂ := b0e162225 X1 X0
           grind)
        | exact superpose b0e162225 b0e14
        | (have j0 := b0e14 (σ X1) (σ X0)
           have j1 := b0e162225 X1 X0
           grind)
        | (have r₁ := b0e14 (σ X0) (σ X1)
           have r₂ := b0e162225 X0 X1
           grind)
        | exact resolve b0e14 b0e162225
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e210090 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e210063 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e210063
      have b0e210105 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e210090 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e210090
        | (have j0 := b0e210090 X0 X1
           grind)
        | exact resolve b0e210090 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e210090
      have b0e210416 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e162225 X1 X0
           have i₂ := b0e210105 X1 X0
           grind)
        | exact superpose b0e210105 b0e162225
        | (have j0 := b0e162225 X1 X0
           have j1 := b0e210105 X0 X1
           grind)
        | exact resolve b0e162225 b0e210105
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e162225 b0e210105
      have b0e210548 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e210416 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e210416
      have b0e213875 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e210548 (τ X0) X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e210548
        | exact resolve b0e210548 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e214000 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (σ X1) (σ X0)
           have i₂ := b0e210548 X1 X0
           grind)
        | exact superpose b0e210548 b0e14
        | (have j0 := b0e14 (σ X1) (σ X0)
           have j1 := b0e210548 X1 X0
           grind)
        | exact resolve b0e14 b0e210548
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e210548
      have b0e214052 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e214000 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e214000
        | (have j0 := b0e214000 X0 X1
           grind)
        | exact resolve b0e214000 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e214000
      have b0e214053 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e214052 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e214052
      have b0e214128 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e213875 X0 X1
           have i₂ := b0e28 X0 X1
           grind)
        | exact superpose b0e28 b0e213875
        | (have j0 := b0e213875 X0 X1
           grind)
        | exact resolve b0e213875 b0e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28 b0e213875
      have b0e214150 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e214128 X0 X1
           have i₂ := b0e27 X0 X1
           grind)
        | exact superpose b0e27 b0e214128
        | (have j0 := b0e214128 X0 X1
           grind)
        | exact resolve b0e214128 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27 b0e214128
      have b0e215735 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e214150 X0 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e214150
        | exact resolve b0e214150 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e214150
      have b0e216391 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e214053 X0 X1
           have i₂ := b0e215735 X1 X0
           grind)
        | exact superpose b0e215735 b0e214053
        | (have j0 := b0e214053 X0 X1
           have j1 := b0e215735 X1 X0
           grind)
        | exact resolve b0e214053 b0e215735
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e214053 b0e215735
      have b0e216484 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e216391 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e216391
      have b0e216744 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e3327 X0
           have i₂ := b0e216484 X0 X0
           grind)
        | exact superpose b0e216484 b0e3327
        | (have j0 := b0e3327 X0
           have j1 := b0e216484 X0 X0
           grind)
        | (have r₁ := b0e3327 X0
           have r₂ := b0e216484 X0 X0
           grind)
        | exact resolve b0e3327 b0e216484
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3327 b0e216484
      have b0e216806 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e216744 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e216744
      have b0e220190 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e259 X1 (σ X0)
           have i₂ := b0e216806 X0
           grind)
        | exact superpose b0e216806 b0e259
        | (have j1 := b0e216806 X0
           grind)
        | exact resolve b0e259 b0e216806
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e220215 : ∀ X0 : G, (M.op (σ X0) y) = (k (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e182971 (σ X0)
           have i₂ := b0e216806 X0
           grind)
        | exact superpose b0e216806 b0e182971
        | (have j1 := b0e216806 X0
           grind)
        | exact resolve b0e182971 b0e216806
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e182971
      have b0e220242 : ∀ X0 X1 : G, (M.op (σ X0) y) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e403 (σ X0) (σ X0) X1
           have i₂ := b0e216806 X0
           grind)
        | exact superpose b0e216806 b0e403
        | (have j1 := b0e216806 X0
           grind)
        | exact resolve b0e403 b0e216806
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e220294 : ∀ X0 : G, (M.op (σ X0) y) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e220215 X0
           have i₂ := b0e17 X0 X0
           grind)
        | exact superpose b0e17 b0e220215
        | (have j0 := b0e220215 X0
           grind)
        | exact resolve b0e220215 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e220215
      have b0e222856 : ∀ X0 : G, (σ X0) = (M.op (σ X0) y) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e216806 X0
           have i₂ := b0e220190 X0 (σ X0)
           grind)
        | exact superpose b0e220190 b0e216806
        | (have j0 := b0e216806 X0
           have j1 := b0e220190 X0 x
           grind)
        | exact resolve b0e216806 b0e220190
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e216806 b0e220190
      have b0e223019 : ∀ X0 : G, (σ X0) = (M.op (σ X0) y) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e222856 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e222856
      have b0e223134 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e4880 X1 (σ X0)
           have i₂ := b0e223019 X0
           grind)
        | exact superpose b0e223019 b0e4880
        | (have j1 := b0e223019 X0
           grind)
        | exact resolve b0e4880 b0e223019
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4880
      have b0e223184 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = (M.op (τ (σ X0)) y) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e50630 (σ X0) X1
           have i₂ := b0e223019 X0
           grind)
        | exact superpose b0e223019 b0e50630
        | (have j1 := b0e223019 X0
           grind)
        | exact resolve b0e50630 b0e223019
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50630
      have b0e223189 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e52152 (σ X0) X1
           have i₂ := b0e223019 X0
           grind)
        | exact superpose b0e223019 b0e52152
        | (have j1 := b0e223019 X0
           grind)
        | exact resolve b0e52152 b0e223019
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52152
      have b0e223191 : ∀ X0 X1 : G, (τ (τ (σ X0))) = (M.op (τ (τ (σ X0))) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e53828 (σ X0) X1
           have i₂ := b0e223019 X0
           grind)
        | exact superpose b0e223019 b0e53828
        | (have j1 := b0e223019 X0
           grind)
        | exact resolve b0e53828 b0e223019
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53828
      have b0e223227 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e403 (σ X0) y x
           have i₂ := b0e223019 X0
           grind)
        | exact superpose b0e223019 b0e403
        | (have j1 := b0e223019 X0
           grind)
        | exact resolve b0e403 b0e223019
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223019
      have b0e223393 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e223191 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e223191
        | (have j0 := b0e223191 X0 X1
           grind)
        | exact resolve b0e223191 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223191
      have b0e223395 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e223189 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e223189
        | (have j0 := b0e223189 X0 X1
           grind)
        | exact resolve b0e223189 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223189
      have b0e223400 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e223184 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e223184
        | (have j0 := b0e223184 X0 X1
           grind)
        | exact resolve b0e223184 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223184
      have b0e223417 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e223134 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e223134
        | (have j0 := b0e223134 X0 X1
           grind)
        | exact resolve b0e223134 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223134
      have b0e226006 : (σ (M.op x y)) ≠ (σ x) ∨ (k x x) = (M.op x x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e223227 x (σ y)
           grind)
        | exact superpose b0e223227 b0e18
        | (have j1 := b0e223227 x x
           grind)
        | exact resolve b0e18 b0e223227
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223227
      have b0e227251 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e223393 (σ X0) X1
           grind)
        | exact superpose b0e223393 b0e17
        | (have j1 := b0e223393 (σ X0) X1
           grind)
        | exact resolve b0e17 b0e223393
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223393
      have b0e227301 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e227251 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e227251
        | (have j0 := b0e227251 X0 X1
           grind)
        | exact resolve b0e227251 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e227251
      have b0e230829 : ∀ X0 : G, (σ x) ≠ (σ (M.op x X0)) ∨ (k x x) = (M.op x x) ∨ (k x x) = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e226006
           have i₂ := b0e223400 x X0
           grind)
        | (have i₁ := b0e226006
           have i₂ := b0e223400 x y
           grind)
        | exact superpose b0e223400 b0e226006
        | (have j1 := b0e223400 x x
           grind)
        | exact resolve b0e226006 b0e223400
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223400 b0e226006
      have b0e230830 : ∀ X0 : G, (σ x) ≠ (σ (M.op x X0)) ∨ (k x x) = (M.op x x) := by
        intro X0
        first
        | (have j0 := b0e230829 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e230829
      have b0e232401 : (σ x) ≠ (σ x) ∨ (k x x) = (M.op x x) ∨ (k x x) = (M.op x x) := by
        first
        | (have i₁ := b0e230830 x
           have i₂ := b0e223395 x x
           grind)
        | exact superpose b0e223395 b0e230830
        | (have j1 := b0e223395 x x
           grind)
        | exact resolve b0e230830 b0e223395
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223395 b0e230830
      have b0e232479 : (σ x) ≠ (σ x) ∨ (k x x) = (M.op x x) := by grind
      clear b0e232401
      have b0e232480 : (k x x) = (M.op x x) := by grind
      clear b0e232479
      have b0e238720 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 (σ (k X0 X0))) ∨ (M.op X0 X2) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e259 X1 (σ X0)
           have i₂ := b0e227301 X0 X2
           grind)
        | exact superpose b0e227301 b0e259
        | (have j1 := b0e227301 X0 X2
           grind)
        | exact resolve b0e259 b0e227301
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e227301
      have b0e244508 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (σ (M.op x x))) ∨ x = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e238720 x X0 X1
           have i₂ := b0e232480
           grind)
        | exact superpose b0e232480 b0e238720
        | (have j0 := b0e238720 x X1 X1
           grind)
        | exact resolve b0e238720 b0e232480
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e232480 b0e238720
      have b0e253763 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e220242 X0 X1
           have i₂ := b0e220242 X0 X2
           grind)
        | (have i₁ := b0e220242 X0 X1
           have i₂ := b0e220242 X0 y
           grind)
        | exact superpose b0e220242 b0e220242
        | (have j0 := b0e220242 X0 X1
           have j1 := b0e220242 X0 X1
           grind)
        | exact resolve b0e220242 b0e220242
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e220242
      have b0e254019 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e253763 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e253763
      have b0e254104 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) y)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e12 (k X0 X0)
           have i₂ := b0e220294 X0
           grind)
        | exact superpose b0e220294 b0e12
        | (have j1 := b0e220294 X0
           grind)
        | exact resolve b0e12 b0e220294
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e220294
      have b0e258757 : ∀ X0 : G, (τ (M.op (σ X0) y)) = X0 ∨ (M.op X0 X0) = (τ (M.op (σ X0) y)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e223417 X0 X0
           have i₂ := b0e254104 X0
           grind)
        | exact superpose b0e254104 b0e223417
        | (have j0 := b0e223417 X0 x
           have j1 := b0e254104 X0
           grind)
        | exact resolve b0e223417 b0e254104
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223417
      have b0e258821 : ∀ X0 : G, (M.op X0 X0) ≠ (τ (M.op (σ X0) y)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e254104 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e254104
      have b0e258841 : ∀ X0 : G, (τ (M.op (σ X0) y)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e258757 X0
           have j1 := b0e258821 X0
           grind)
        | (have r₁ := b0e258757 X0
           have r₂ := b0e258821 X0
           grind)
        | exact resolve b0e258757 b0e258821
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e258757
      have b0e259002 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e258841 X0
           have i₂ := b0e254019 X0 X1 y
           grind)
        | (have i₁ := b0e258841 X0
           have i₂ := b0e254019 X0 y X1
           grind)
        | exact superpose b0e254019 b0e258841
        | (have j0 := b0e258841 X0
           have j1 := b0e254019 X0 X1 x
           grind)
        | exact resolve b0e258841 b0e254019
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e254019 b0e258841
      have b0e259143 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e259002 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e259002
      have b0e269203 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e258821 X0
           have i₂ := b0e259143 X0 y
           grind)
        | exact superpose b0e259143 b0e258821
        | (have j0 := b0e258821 X0
           have j1 := b0e259143 X0 x
           grind)
        | exact resolve b0e258821 b0e259143
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e258821 b0e259143
      have b0e269204 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e269203 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e269203
      have b0e269212 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e269204 X0
           have j1 := b0e12531 X0
           grind)
        | (have r₁ := b0e269204 X0
           have r₂ := b0e12531 X0
           grind)
        | exact resolve b0e269204 b0e12531
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12531 b0e269204
      have b0e269520 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e269212 (σ X0)
           grind)
        | exact superpose b0e269212 b0e17
        | exact resolve b0e17 b0e269212
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e269615 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e269520 X0
           have i₂ := b0e269212 X0
           grind)
        | exact superpose b0e269212 b0e269520
        | exact resolve b0e269520 b0e269212
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e269212 b0e269520
      have b0e270561 : ∀ X0 : G, (M.op (σ (M.op x x)) y) = (σ (M.op (M.op x x) (M.op x x))) ∨ x = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e244508 (σ (M.op x x)) X0
           have i₂ := b0e269615 (M.op x x)
           grind)
        | exact superpose b0e269615 b0e244508
        | (have j0 := b0e244508 X0 X0
           grind)
        | exact resolve b0e244508 b0e269615
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e244508
      have b0e270650 : ∀ X0 X1 : G, (M.op (σ X0) y) = (M.op (σ (M.op X0 X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e403 (σ X0) (σ X0) X1
           have i₂ := b0e269615 X0
           grind)
        | exact superpose b0e269615 b0e403
        | exact resolve b0e403 b0e269615
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e269615
      have b0e270766 : ∀ X0 : G, (M.op (σ (M.op x x)) y) = (σ (M.op (M.op x x) y)) ∨ x = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e270561 X0
           have i₂ := b0e259 (M.op x x) x
           grind)
        | exact superpose b0e259 b0e270561
        | (have j0 := b0e270561 X0
           grind)
        | exact resolve b0e270561 b0e259
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e259 b0e270561
      have b0e270874 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x x)) y) ∨ x = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e270766 X0
           have i₂ := b0e403 x x y
           grind)
        | exact superpose b0e403 b0e270766
        | (have j0 := b0e270766 X0
           grind)
        | exact resolve b0e270766 b0e403
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e403 b0e270766
      have b0e270920 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) y) ∨ x = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e270874 X0
           have i₂ := b0e270650 x y
           grind)
        | exact superpose b0e270650 b0e270874
        | (have j0 := b0e270874 X0
           grind)
        | exact resolve b0e270874 b0e270650
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e270650 b0e270874
      have b0e270948 : ∀ X0 : G, x = (M.op x X0) := by
        intro X0
        first
        | (have j0 := b0e270920 X0
           grind)
        | (have r₁ := b0e270920 X0
           have r₂ := b0e1911
           grind)
        | exact resolve b0e270920 b0e1911
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e270920
      have b0e271113 : (σ x) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e1911
           have i₂ := b0e270948 y
           grind)
        | exact superpose b0e270948 b0e1911
        | exact resolve b0e1911 b0e270948
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1911
      have b0e271513 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e35431 x x
           have i₂ := b0e270948 y
           grind)
        | exact superpose b0e270948 b0e35431
        | exact resolve b0e35431 b0e270948
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35431 b0e270948
      have b0e271643 : False := by grind
      exact b0e271643
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
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
        have b1e26 : x = (k x y) := by grind
        clear b1e24
        have b1e38 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 y X0 x X1
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
          intro X0 X2
          first
          | (have i₁ := b1e38 x X2
             have i₂ := b1e38 x X0
             grind)
          | (have i₁ := b1e38 X0 x
             have i₂ := b1e38 X0 (M.op X0 X0)
             grind)
          | exact superpose b1e38 b1e38
          | exact resolve b1e38 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b1e107 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e20
             have i₂ := b1e50 x X0
             grind)
          | (have i₁ := b1e20
             have i₂ := b1e50 X0 x
             grind)
          | exact superpose b1e50 b1e20
          | exact resolve b1e20 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e121 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
        have b1e125 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e121
             have r₂ := b1e21
             grind)
          | exact resolve b1e121 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e121
        have b1e128 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e125
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e125
          | exact resolve b1e125 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e125
        have b1e131 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e128
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e128
          | exact resolve b1e128 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e128
        have b1e144 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e15 X0 y
             have i₂ := b1e107 X0
             grind)
          | exact superpose b1e107 b1e15
          | (have j0 := b1e15 X0 y
             grind)
          | (have r₁ := b1e15 X0 y
             have r₂ := b1e107 X0
             grind)
          | exact resolve b1e15 b1e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e107
        have b1e148 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b1e144 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e144
        have b1e151 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e131
             grind)
          | exact superpose b1e131 b1e21
          | exact resolve b1e21 b1e131
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e131
        have b1e3685 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e71 y y
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e71
          | exact resolve b1e71 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71
        have b1e3823 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by grind
        clear b1e3685
        have b1e3897 : (σ x) = (σ (k y y)) := by
          first
          | (have r₁ := b1e3823
             have r₂ := b1e151
             grind)
          | exact resolve b1e3823 b1e151
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3823
        have b1e3968 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e3897
             have i₂ := b1e148 y
             grind)
          | exact superpose b1e148 b1e3897
          | exact resolve b1e3897 b1e148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e148 b1e3897
        have b1e3992 : False := by grind
        exact b1e3992
      · have b2e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op y x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
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
        have b2e29 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X2 X4) X5) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b2e12 X2 (M.op X0 x) X4 X5
             have i₂ := b2e12 X0 X1 x (M.op X0 x)
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 y X0 x X1
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X0 X1 x x
             have i₂ := b2e12 X0 X2 x x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
          intro X0 X2
          first
          | (have i₁ := b2e32 x X2
             have i₂ := b2e32 x X0
             grind)
          | (have i₁ := b2e32 X0 x
             have i₂ := b2e32 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e32 b2e32
          | exact resolve b2e32 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e66 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (σ y)
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (M.op (σ y) (σ y)) x
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
        have b2e86 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e20
             have i₂ := b2e41 x X0
             grind)
          | (have i₁ := b2e20
             have i₂ := b2e41 X0 x
             grind)
          | exact superpose b2e41 b2e20
          | exact resolve b2e20 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e96 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e98 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e96 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e96
        have b2e223 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b2e35 X0 X1 y
             have i₂ := b2e86 y
             grind)
          | exact superpose b2e86 b2e35
          | exact resolve b2e35 b2e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e319 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op X3 y)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e29 X3 y X0 X1 X2
             have i₂ := b2e86 y
             grind)
          | exact superpose b2e86 b2e29
          | exact resolve b2e29 b2e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e332 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e29 y x X0 X1 X2
             have i₂ := b2e86 (M.op x x)
             grind)
          | exact superpose b2e86 b2e29
          | exact resolve b2e29 b2e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29 b2e86
        have b2e422 : ∀ X0 X3 : G, (M.op X0 y) = (M.op X0 (M.op X3 y)) := by
          intro X0 X3
          first
          | (have i₁ := b2e319 X0 x x X3
             have i₂ := b2e332 X0 x x
             grind)
          | exact superpose b2e332 b2e319
          | exact resolve b2e319 b2e332
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e319
        have b2e1966 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e66 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e1967 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1966
             have r₂ := b2e21
             grind)
          | exact resolve b2e1966 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1966
        have b2e1968 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1967
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1967
          | exact resolve b2e1967 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1967
        have b2e1969 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1968
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e1968
          | exact resolve b2e1968 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e1968
        have b2e1970 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e1969
             grind)
          | exact superpose b2e1969 b2e19
          | exact resolve b2e19 b2e1969
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1980 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) y) := by
          intro X0
          first
          | (have i₁ := b2e332 (σ x) (σ y) X0
             have i₂ := b2e1969
             grind)
          | exact superpose b2e1969 b2e332
          | exact resolve b2e332 b2e1969
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e332
        have b2e3221 : (σ x) = (M.op (σ x) y) := by
          first
          | (have i₁ := b2e1969
             have i₂ := b2e1980 (σ y)
             grind)
          | exact superpose b2e1980 b2e1969
          | exact resolve b2e1969 b2e1980
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1969
        have b2e3228 : (M.op (σ x) (M.op (σ x) y)) = (k (M.op (σ x) y) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) y)) := by grind
        clear b2e1980
        have b2e3285 : (M.op (σ x) y) = (k (M.op (σ x) y) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) y)) := by
          first
          | (have i₁ := b2e3228
             have i₂ := b2e422 (σ x) (σ x)
             grind)
          | exact superpose b2e422 b2e3228
          | exact resolve b2e3228 b2e422
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e422 b2e3228
        have b2e3292 : (M.op (σ x) y) = (k (M.op (σ x) y) (σ x)) := by
          first
          | (have j1 := b2e15 (M.op (σ x) y) (σ x)
             grind)
          | (have r₁ := b2e3285
             have r₂ := b2e15 (M.op (σ x) y) (σ x)
             grind)
          | exact resolve b2e3285 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3285
        have b2e3294 : (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b2e3292
             have i₂ := b2e3221
             grind)
          | exact superpose b2e3221 b2e3292
          | exact resolve b2e3292 b2e3221
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3221 b2e3292
        have b2e3295 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b2e3294
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e3294
          | exact resolve b2e3294 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3294
        have b2e4384 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b2e13 (k x x)
             have i₂ := b2e3295
             grind)
          | exact superpose b2e3295 b2e13
          | exact resolve b2e13 b2e3295
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3295
        have b2e4397 : x = (k x x) := by
          first
          | (have i₁ := b2e4384
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e4384
          | exact resolve b2e4384 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4384
        have b2e4448 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e98 x x
             have i₂ := b2e4397
             grind)
          | exact superpose b2e4397 b2e98
          | (have j0 := b2e98 x x
             grind)
          | exact resolve b2e98 b2e4397
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e98 b2e4397
        have b2e4449 : x = (M.op x x) := by grind
        clear b2e4448
        have b2e4530 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e223 X0 x
             have i₂ := b2e4449
             grind)
          | exact superpose b2e4449 b2e223
          | exact resolve b2e223 b2e4449
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e223
        have b2e7831 : x = (M.op x y) := by
          first
          | (have i₁ := b2e4449
             have i₂ := b2e4530 x
             grind)
          | exact superpose b2e4530 b2e4449
          | exact resolve b2e4449 b2e4530
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4449 b2e4530
        have b2e7934 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e1970
             have i₂ := b2e7831
             grind)
          | exact superpose b2e7831 b2e1970
          | exact resolve b2e1970 b2e7831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1970 b2e7831
        have b2e7962 : False := by grind
        exact b2e7962
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y x) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
        have b3e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b3e42 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (σ y) X0 (σ x) X1
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e47 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 X2) ∨ (k X3 (M.op X0 X2)) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e15 X3 (M.op X0 X2)
             have i₂ := b3e12 X0 X1 X2 X3
             grind)
          | exact superpose b3e12 b3e15
          | (have j0 := b3e15 X3 (M.op X0 X2)
             grind)
          | (have r₁ := b3e15 X3 (M.op X0 (M.op X1 X1))
             have r₂ := b3e12 X0 X1 (M.op X1 X1) X3
             grind)
          | exact resolve b3e15 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X0 X1
             have i₂ := b3e17 (σ X0) (σ X1)
             grind)
          | exact superpose b3e17 b3e18
          | (have j1 := b3e17 (σ X0) (σ X1)
             grind)
          | exact resolve b3e18 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e92 : (M.op y x) = (k x y) ∨ y = (M.op y x) := by grind
        have b3e94 : (M.op y x) = (k x y) := by
          first
          | (have r₁ := b3e92
             have r₂ := b3e20
             grind)
          | exact resolve b3e92 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e92
        have b3e96 : x = (M.op y x) := by
          first
          | (have i₁ := b3e94
             have i₂ := b3e29
             grind)
          | exact superpose b3e29 b3e94
          | exact resolve b3e94 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e94
        have b3e99 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e96
             grind)
          | exact superpose b3e96 b3e20
          | exact resolve b3e20 b3e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e96
        have b3e114 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k X0 (τ X1))
             have i₂ := b3e32 X1 X0
             grind)
          | exact superpose b3e32 b3e13
          | exact resolve b3e13 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e241 : ∀ X0 X2 : G, (M.op (σ y) X0) = (M.op (σ y) X2) := by
          intro X0 X2
          first
          | (have i₁ := b3e42 x X2
             have i₂ := b3e42 x X0
             grind)
          | (have i₁ := b3e42 X0 x
             have i₂ := b3e42 X0 (M.op X0 X0)
             grind)
          | exact superpose b3e42 b3e42
          | exact resolve b3e42 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1867 : ∀ X0 X2 X3 : G, (M.op (σ y) X0) ≠ (M.op (σ y) X2) ∨ (k X3 (M.op (σ y) X2)) = X3 := by
          intro X0 X2 X3
          first
          | (have i₁ := b3e47 (σ y) x X2 X3
             have i₂ := b3e42 x X0
             grind)
          | (have i₁ := b3e47 (σ y) x X2 X3
             have i₂ := b3e42 X0 (M.op x x)
             grind)
          | exact superpose b3e42 b3e47
          | (have j0 := b3e47 (σ y) x X2 X3
             grind)
          | (have r₁ := b3e47 (σ y) X0 x X3
             have r₂ := b3e42 X0 x
             grind)
          | (have r₁ := b3e47 (σ y) x (M.op X0 X0) X3
             have r₂ := b3e42 X0 (M.op x x)
             grind)
          | exact resolve b3e47 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42 b3e47
        have b3e1925 : ∀ X2 X3 : G, (k X3 (M.op (σ y) X2)) = X3 := by
          intro X2 X3
          first
          | (have j0 := b3e1867 x X2 X3
             grind)
          | (have r₁ := b3e1867 x X2 X3
             have r₂ := b3e241 x X2
             grind)
          | (have r₁ := b3e1867 X2 x X3
             have r₂ := b3e241 x X2
             grind)
          | exact resolve b3e1867 b3e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e241 b3e1867
        have b3e2066 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e1925 (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1925
          | exact resolve b3e1925 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1925
        have b3e2101 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e2066 (σ X0)
             grind)
          | exact superpose b3e2066 b3e18
          | exact resolve b3e18 b3e2066
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2066
        have b3e2668 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e13 (k X0 y)
             have i₂ := b3e2101 X0
             grind)
          | exact superpose b3e2101 b3e13
          | exact resolve b3e13 b3e2101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2101
        have b3e2669 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e2668 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e2668
          | exact resolve b3e2668 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2668
        have b3e3197 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b3e70 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70
        have b3e3198 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b3e3197 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3197
        have b3e5683 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ y)) := by
          intro X0
          first
          | (have i₁ := b3e114 X0 y
             have i₂ := b3e2669 (σ X0)
             grind)
          | exact superpose b3e2669 b3e114
          | exact resolve b3e114 b3e2669
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e114 b3e2669
        have b3e5691 : ∀ X0 : G, (k X0 (τ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e5683 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e5683
          | exact resolve b3e5683 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5683
        have b3e12935 : (σ (τ y)) ≠ (σ (τ y)) ∨ (σ (τ y)) = (M.op (σ (τ y)) (σ (τ y))) := by
          first
          | (have i₁ := b3e3198 (τ y)
             have i₂ := b3e5691 (τ y)
             grind)
          | exact superpose b3e5691 b3e3198
          | (have j0 := b3e3198 (τ y)
             grind)
          | exact resolve b3e3198 b3e5691
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3198 b3e5691
        have b3e12954 : (σ (τ y)) = (M.op (σ (τ y)) (σ (τ y))) := by grind
        clear b3e12935
        have b3e12982 : y = (M.op y y) := by
          first
          | (have i₁ := b3e12954
             have i₂ := b3e14 y
             grind)
          | exact superpose b3e14 b3e12954
          | exact resolve b3e12954 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12954
        have b3e13010 : x = y := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e12982
             grind)
          | exact superpose b3e12982 b3e21
          | exact resolve b3e21 b3e12982
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12982
        have b3e13078 : False := by grind
        exact b3e13078
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y x) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e35 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) X5) = (M.op X3 (M.op (M.op (M.op X0 X0) X1) X2)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e13 X3 (M.op X0 X0) X4 X5
               have i₂ := b4e13 (M.op X0 X0) X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (σ x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 (σ y) X1 X2
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ y) X0 (σ y) X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 y X0 y X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X1 x x
               have i₂ := b4e13 X0 X2 x x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e49 : ∀ X0 X3 X4 X5 : G, (M.op (M.op X3 X4) X5) = (M.op X3 (M.op (M.op X0 X0) (σ x))) := by
            intro X0 X3 X4 X5
            first
            | (have i₁ := b4e35 X0 x x X3 X4 X5
               have i₂ := b4e37 (M.op X0 X0) x x
               grind)
            | exact superpose b4e37 b4e35
            | exact resolve b4e35 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e50 : ∀ X0 X3 X4 X5 : G, (M.op (M.op X3 X4) X5) = (M.op X3 (M.op X0 (σ x))) := by
            intro X0 X3 X4 X5
            first
            | (have i₁ := b4e49 X0 X3 X4 X5
               have i₂ := b4e37 X0 X0 (σ x)
               grind)
            | exact superpose b4e37 b4e49
            | exact resolve b4e49 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49
          have b4e51 : ∀ X0 X3 : G, (M.op X3 (M.op X0 (σ x))) = (M.op X3 (σ x)) := by
            intro X0 X3
            first
            | (have i₁ := b4e50 X0 X3 x x
               have i₂ := b4e37 X3 x x
               grind)
            | exact superpose b4e37 b4e50
            | exact resolve b4e50 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e50
          have b4e55 : ∀ X0 : G, (M.op y x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e43 y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e43
            | exact resolve b4e43 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e120 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
          have b4e122 : (M.op y x) = (k x y) ∨ y = (M.op y x) := by grind
          have b4e124 : (M.op y x) = (k x y) := by
            first
            | (have r₁ := b4e122
               have r₂ := b4e21
               grind)
            | exact resolve b4e122 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e122
          have b4e126 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e120
               have r₂ := b4e23
               grind)
            | exact resolve b4e120 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e120
          have b4e130 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e126
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e126
            | exact resolve b4e126 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e126
          have b4e133 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e130
               have i₂ := b4e124
               grind)
            | exact superpose b4e124 b4e130
            | exact resolve b4e130 b4e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e124 b4e130
          have b4e425 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) x) := by
            intro X0
            first
            | (have i₁ := b4e42 y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e42
            | exact resolve b4e42 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e477 : (σ (M.op x y)) ≠ (M.op (σ y) x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e425 (σ y)
               grind)
            | exact superpose b4e425 b4e20
            | exact resolve b4e20 b4e425
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e425
          have b4e502 : (σ (M.op y x)) ≠ (M.op (σ y) x) := by
            first
            | (have i₁ := b4e477
               have i₂ := b4e55 y
               grind)
            | exact superpose b4e55 b4e477
            | exact resolve b4e477 b4e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55 b4e477
          have b4e556 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 x) := by
            intro X0 X1
            first
            | (have i₁ := b4e44 X0 X1 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e44
            | exact resolve b4e44 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e907 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b4e51 (σ x) X0
               have i₂ := b4e556 X0 (σ x)
               grind)
            | exact superpose b4e556 b4e51
            | exact resolve b4e51 b4e556
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51 b4e556
          have b4e1011 : (σ (M.op y x)) = (M.op (σ y) x) := by
            first
            | (have i₁ := b4e133
               have i₂ := b4e907 (σ y)
               grind)
            | exact superpose b4e907 b4e133
            | exact resolve b4e133 b4e907
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e133 b4e907
          have b4e1019 : False := by grind
          exact b4e1019
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : y ≠ (M.op y x) := by grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e37 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 y X0 y X1
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e46 : ∀ X0 : G, (M.op y x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e37 y X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e37
            | exact resolve b5e37 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e87 : (M.op y x) = (k x y) ∨ y = (M.op y x) := by grind
          have b5e89 : (M.op y x) = (k x y) := by
            first
            | (have r₁ := b5e87
               have r₂ := b5e21
               grind)
            | exact resolve b5e87 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e87
          have b5e3840 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e63 x y
               grind)
            | exact superpose b5e63 b5e20
            | (have j1 := b5e63 x y
               grind)
            | exact resolve b5e20 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e3998 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e3840
               have r₂ := b5e24
               grind)
            | exact resolve b5e3840 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3840
          have b5e4045 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b5e3998
               have r₂ := b5e23
               grind)
            | exact resolve b5e3998 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3998
          have b5e4063 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b5e4045
               have i₂ := b5e89
               grind)
            | exact superpose b5e89 b5e4045
            | exact resolve b5e4045 b5e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e89 b5e4045
          have b5e4073 : (σ (M.op y x)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b5e4063
               have i₂ := b5e46 y
               grind)
            | exact superpose b5e46 b5e4063
            | exact resolve b5e4063 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46 b5e4063
          have b5e4074 : False := by grind
          exact b5e4074
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y x) := by grind
        have b6e21 : x ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
        have b6e27 : (k x y) = (τ (σ x)) := by
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
        have b6e28 : x = (k x y) := by
          first
          | (have i₁ := b6e27
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e27
          | exact resolve b6e27 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e18
          | exact resolve b6e18 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e40 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X2 X4) X5) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b6e12 X2 (M.op X0 x) X4 X5
             have i₂ := b6e12 X0 X1 x (M.op X0 x)
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e43 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (σ y) X0 (σ x) X1
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e46 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
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
        have b6e55 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k X0 (τ X1))
             have i₂ := b6e31 X1 X0
             grind)
          | exact superpose b6e31 b6e13
          | exact resolve b6e13 b6e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b6e66 : x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e28
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e28
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e28 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e74 : x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e66
             have r₂ := b6e21
             grind)
          | exact resolve b6e66 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e77 : x = (M.op x y) := by
          first
          | (have r₁ := b6e74
             have r₂ := b6e20
             grind)
          | exact resolve b6e74 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e138 : ∀ X0 X2 : G, (M.op (σ y) X0) = (M.op (σ y) X2) := by
          intro X0 X2
          first
          | (have i₁ := b6e43 x X2
             have i₂ := b6e43 x X0
             grind)
          | (have i₁ := b6e43 X0 x
             have i₂ := b6e43 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e43 b6e43
          | exact resolve b6e43 b6e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e180 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b6e22
             have i₂ := b6e138 (σ x) X0
             grind)
          | (have i₁ := b6e22
             have i₂ := b6e138 X0 (σ x)
             grind)
          | exact superpose b6e138 b6e22
          | exact resolve b6e22 b6e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e220 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (M.op (σ y) X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e46 X1 X2 (σ y)
             have i₂ := b6e138 (σ y) X0
             grind)
          | (have i₁ := b6e46 X1 X2 (σ y)
             have i₂ := b6e138 X0 (σ y)
             grind)
          | exact superpose b6e138 b6e46
          | exact resolve b6e46 b6e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e138
        have b6e264 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ y)) := by
          intro X1 X2
          first
          | (have i₁ := b6e220 x X1 X2
             have i₂ := b6e180 x
             grind)
          | exact superpose b6e180 b6e220
          | exact resolve b6e220 b6e180
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e220
        have b6e283 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e15 X0 (σ y)
             have i₂ := b6e180 X0
             grind)
          | exact superpose b6e180 b6e15
          | (have j0 := b6e15 X0 (σ y)
             grind)
          | (have r₁ := b6e15 X0 (σ y)
             have r₂ := b6e180 X0
             grind)
          | exact resolve b6e15 b6e180
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e289 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (σ y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X0 (σ y) X1 X2
             have i₂ := b6e180 (σ y)
             grind)
          | exact superpose b6e180 b6e12
          | exact resolve b6e12 b6e180
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e293 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b6e283 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e283
        have b6e311 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op x (M.op X1 (M.op X2 X2))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e40 X1 X2 x y X0
             have i₂ := b6e77
             grind)
          | exact superpose b6e77 b6e40
          | exact resolve b6e40 b6e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e330 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op X3 (σ y))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e40 X3 (σ y) X0 X1 X2
             have i₂ := b6e180 (σ y)
             grind)
          | exact superpose b6e180 b6e40
          | exact resolve b6e40 b6e180
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e180
        have b6e412 : ∀ X0 X3 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X3 (σ y))) := by
          intro X0 X3
          first
          | (have i₁ := b6e330 X0 x x X3
             have i₂ := b6e289 X0 x x
             grind)
          | exact superpose b6e289 b6e330
          | exact resolve b6e330 b6e289
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e289 b6e330
        have b6e426 : ∀ X0 X1 : G, (M.op x X0) = (M.op x (M.op X1 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b6e311 X0 X1 x
             have i₂ := b6e264 X1 x
             grind)
          | exact superpose b6e264 b6e311
          | exact resolve b6e311 b6e264
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e264 b6e311
        have b6e453 : ∀ X0 : G, (M.op x X0) = (M.op x (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e426 X0 x
             have i₂ := b6e412 x x
             grind)
          | exact superpose b6e412 b6e426
          | exact resolve b6e426 b6e412
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e412 b6e426
        have b6e486 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 y
             have i₂ := b6e293 (σ X0)
             grind)
          | exact superpose b6e293 b6e18
          | exact resolve b6e18 b6e293
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e293
        have b6e691 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b6e13 (k X0 y)
             have i₂ := b6e486 X0
             grind)
          | exact superpose b6e486 b6e13
          | exact resolve b6e13 b6e486
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e486
        have b6e692 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e691 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e691
          | exact resolve b6e691 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e691
        have b6e1391 : ∀ X0 X1 : G, (M.op x X1) = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e453 X1
             have i₂ := b6e453 X0
             grind)
          | (have i₁ := b6e453 X0
             have i₂ := b6e453 (σ y)
             grind)
          | exact superpose b6e453 b6e453
          | exact resolve b6e453 b6e453
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e453
        have b6e1504 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (M.op x X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e46 X1 X2 x
             have i₂ := b6e1391 X0 x
             grind)
          | (have i₁ := b6e46 X1 X2 x
             have i₂ := b6e1391 x X0
             grind)
          | exact superpose b6e1391 b6e46
          | exact resolve b6e46 b6e1391
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46
        have b6e1527 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e77
             have i₂ := b6e1391 X0 y
             grind)
          | (have i₁ := b6e77
             have i₂ := b6e1391 y X0
             grind)
          | exact superpose b6e1391 b6e77
          | exact resolve b6e77 b6e1391
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77 b6e1391
        have b6e1567 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 x) := by
          intro X1 X2
          first
          | (have i₁ := b6e1504 x X1 X2
             have i₂ := b6e1527 x
             grind)
          | exact superpose b6e1527 b6e1504
          | exact resolve b6e1504 b6e1527
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1504 b6e1527
        have b6e2815 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e64 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e2816 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e2815 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2815
        have b6e4738 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ y)) := by
          intro X0
          first
          | (have i₁ := b6e55 X0 y
             have i₂ := b6e692 (σ X0)
             grind)
          | exact superpose b6e692 b6e55
          | exact resolve b6e55 b6e692
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55 b6e692
        have b6e4746 : ∀ X0 : G, (k X0 (τ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e4738 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e4738
          | exact resolve b6e4738 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4738
        have b6e11636 : (σ (τ y)) ≠ (σ (τ y)) ∨ (σ (τ y)) = (M.op (σ (τ y)) (σ (τ y))) := by
          first
          | (have i₁ := b6e2816 (τ y)
             have i₂ := b6e4746 (τ y)
             grind)
          | exact superpose b6e4746 b6e2816
          | (have j0 := b6e2816 (τ y)
             grind)
          | exact resolve b6e2816 b6e4746
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2816 b6e4746
        have b6e11650 : (σ (τ y)) = (M.op (σ (τ y)) (σ (τ y))) := by grind
        clear b6e11636
        have b6e11673 : y = (M.op y y) := by
          first
          | (have i₁ := b6e11650
             have i₂ := b6e14 y
             grind)
          | exact superpose b6e14 b6e11650
          | exact resolve b6e11650 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e11650
        have b6e11720 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b6e1567 X0 y
             have i₂ := b6e11673
             grind)
          | exact superpose b6e11673 b6e1567
          | exact resolve b6e1567 b6e11673
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1567
        have b6e12434 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e11720 y
             grind)
          | exact superpose b6e11720 b6e20
          | exact resolve b6e20 b6e11720
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e11720
        have b6e12435 : False := by grind
        exact b6e12435
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op y x) := by grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (σ x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X0 (σ y) X1 X2
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ y) X0 (σ y) X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e77 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
          have b7e85 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e77
               have r₂ := b7e23
               grind)
            | exact resolve b7e77 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e88 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e85
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e85
            | exact resolve b7e85 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e99 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 x x
               have i₂ := b7e30 X0 x x
               grind)
            | exact superpose b7e30 b7e13
            | exact resolve b7e13 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e235 : ∀ X0 X2 : G, (M.op (σ x) X0) = (M.op (σ x) X2) := by
            intro X0 X2
            first
            | (have i₁ := b7e35 x X2
               have i₂ := b7e35 x X0
               grind)
            | exact superpose b7e35 b7e35
            | exact resolve b7e35 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e300 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e20
               have i₂ := b7e235 (σ y) X0
               grind)
            | (have i₁ := b7e20
               have i₂ := b7e235 X0 (σ y)
               grind)
            | exact superpose b7e235 b7e20
            | exact resolve b7e20 b7e235
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e235
          have b7e464 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e300 x
               have i₂ := b7e35 X0 x
               grind)
            | exact superpose b7e35 b7e300
            | exact resolve b7e300 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35 b7e300
          have b7e470 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e464 x
               have i₂ := b7e99 (σ y) x
               grind)
            | exact superpose b7e99 b7e464
            | exact resolve b7e464 b7e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99 b7e464
          have b7e471 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b7e470
               have i₂ := b7e88
               grind)
            | exact superpose b7e88 b7e470
            | exact resolve b7e470 b7e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88 b7e470
          have b7e472 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e471
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e471
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e471 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e471
          have b7e473 : x = (M.op y y) ∨ y = (M.op y x) := by grind
          clear b7e472
          have b7e474 : y = (M.op y x) := by
            first
            | (have r₁ := b7e473
               have r₂ := b7e22
               grind)
            | exact resolve b7e473 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e473
          have b7e475 : False := by grind
          exact b7e475
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y x) := by grind
          have b8e22 : x ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e53 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
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
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1018 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e53 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e1019 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1018
               have r₂ := b8e23
               grind)
            | exact resolve b8e1018 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1018
          have b8e1020 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1019
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1019
            | exact resolve b8e1019 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1019
          have b8e1021 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1020
               grind)
            | exact superpose b8e1020 b8e20
            | exact resolve b8e20 b8e1020
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1020
          have b8e1228 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e1021
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1021
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1021 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1021
          have b8e1229 : x = (M.op y y) ∨ y = (M.op y x) := by grind
          clear b8e1228
          have b8e1231 : y = (M.op y x) := by
            first
            | (have r₁ := b8e1229
               have r₂ := b8e22
               grind)
            | exact resolve b8e1229 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1229
          have b8e1233 : False := by grind
          exact b8e1233

/-- `Equation4494`: `x ◇ (y ◇ y) = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_x_pyx_pxy_Equation4494 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4494 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4494.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op y x) (x) with h2a | h2a
      · have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op x y) := by grind
        have b0e21 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e24 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e19
          | exact resolve b0e19 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e25 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b0e24
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e24
          | exact resolve b0e24 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e24
        have b0e26 : False := by grind
        exact b0e26
      · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
        · have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e21 : y = (M.op x y) := by grind
          have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e26 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e20
            | exact resolve b1e20 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e27 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b1e26
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e26
            | exact resolve b1e26 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e26
          have b1e28 : False := by grind
          exact b1e28
        · have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : y = (M.op x y) := by grind
          have b2e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e26 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e20
            | exact resolve b2e20 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e27 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b2e26
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e26
            | exact resolve b2e26 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e26
          have b2e28 : False := by grind
          exact b2e28
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op y x) (x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
            intro X0 X1 X2
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e21 : y = (M.op x y) := by grind
          have b3e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e23 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e27 : y ≠ y ∨ x = (k x y) := by
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
          have b3e31 : x = (k x y) := by grind
          clear b3e27
          have b3e78 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          have b3e80 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e78
               have r₂ := b3e22
               grind)
            | exact resolve b3e78 b3e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e78
          have b3e81 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b3e80
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e80
            | exact resolve b3e80 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e80
          have b3e82 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b3e81
               have i₂ := b3e31
               grind)
            | exact superpose b3e31 b3e81
            | exact resolve b3e81 b3e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e31 b3e81
          have b3e87 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op (σ x) (σ x))) := by
            intro X0
            first
            | (have i₁ := b3e13 X0 (σ x) (σ y)
               have i₂ := b3e82
               grind)
            | exact superpose b3e82 b3e13
            | exact resolve b3e13 b3e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e82
          have b3e91 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b3e87 X0
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e87
            | exact resolve b3e87 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e87
          have b3e100 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e91 (σ x)
               grind)
            | exact superpose b3e91 b3e22
            | (have r₁ := b3e22
               have r₂ := b3e91 (σ x)
               grind)
            | exact resolve b3e22 b3e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e91
          have b3e101 : False := by grind
          exact b3e101
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b4e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
              intro X0 X1 X2
              grind
            have b4e22 : y = (M.op x y) := by grind
            have b4e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
            have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b4e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e44 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y y)) := by
              intro X0
              first
              | (have i₁ := b4e14 X0 y x
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e14
              | exact resolve b4e14 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e45 : ∀ X0 : G, (M.op x y) = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b4e14 X0 y y
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e14
              | exact resolve b4e14 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e50 : ∀ X0 : G, y = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b4e45 X0
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e45
              | exact resolve b4e45 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e45
            have b4e51 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b4e44 X0
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e44
              | exact resolve b4e44 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e44
            have b4e52 : x = y := by
              first
              | (have i₁ := b4e51 x
                 have i₂ := b4e50 x
                 grind)
              | exact superpose b4e50 b4e51
              | exact resolve b4e51 b4e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e50 b4e51
            have b4e54 : (σ y) ≠ (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b4e23
                 have i₂ := b4e52
                 grind)
              | exact superpose b4e52 b4e23
              | exact resolve b4e23 b4e52
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e55 : (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b4e24
                 have i₂ := b4e52
                 grind)
              | exact superpose b4e52 b4e24
              | exact resolve b4e24 b4e52
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e52
            have b4e61 : False := by grind
            exact b4e61
          · have b5e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
              intro X0 X1 X2
              grind
            have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : y = (M.op x y) := by grind
            have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
            have b5e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e29 : y ≠ y ∨ x = (k x y) := by
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
            have b5e31 : x = (k x y) := by grind
            clear b5e29
            have b5e45 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (σ x)) := by
              intro X0
              first
              | (have i₁ := b5e14 X0 (σ x) (σ x)
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e14
              | exact resolve b5e14 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e84 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
            have b5e89 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e84
                 have r₂ := b5e23
                 grind)
              | exact resolve b5e84 b5e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e84
            have b5e90 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b5e89
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e89
              | exact resolve b5e89 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e89
            have b5e91 : (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b5e90
                 have i₂ := b5e31
                 grind)
              | exact superpose b5e31 b5e90
              | exact resolve b5e90 b5e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e31 b5e90
            have b5e92 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op (σ x) (σ x))) := by
              intro X0
              first
              | (have i₁ := b5e14 X0 (σ x) (σ y)
                 have i₂ := b5e91
                 grind)
              | exact superpose b5e91 b5e14
              | exact resolve b5e14 b5e91
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e96 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b5e92 X0
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e92
              | exact resolve b5e92 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e92
            have b5e121 : (σ y) ≠ (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b5e23
                 have i₂ := b5e45 (σ x)
                 grind)
              | exact superpose b5e45 b5e23
              | exact resolve b5e23 b5e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e122 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b5e91
                 have i₂ := b5e45 X0
                 grind)
              | exact superpose b5e45 b5e91
              | exact resolve b5e91 b5e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e45
            have b5e127 : (σ x) = (σ y) := by
              first
              | (have i₁ := b5e122 x
                 have i₂ := b5e96 x
                 grind)
              | exact superpose b5e96 b5e122
              | exact resolve b5e122 b5e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e96 b5e122
            have b5e128 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b5e121
                 have i₂ := b5e91
                 grind)
              | exact superpose b5e91 b5e121
              | exact resolve b5e121 b5e91
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e91 b5e121
            have b5e137 : False := by grind
            exact b5e137
      · rcases eq_or_ne (M.op y x) (x) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
            intro X0 X1 X2
            grind
          have b6e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b6e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : y = (M.op x y) := by grind
          have b6e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b6e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e27 : y ≠ y ∨ x = (k x y) := by
            first
            | (have i₁ := b6e16 x y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e16
            | (have j0 := b6e16 x y
               grind)
            | (have r₁ := b6e16 x y
               have r₂ := b6e21
               grind)
            | exact resolve b6e16 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e30 : x = (k x y) := by grind
          clear b6e27
          have b6e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 (τ X0) X1
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e19
            | exact resolve b6e19 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 X1 (τ X0)
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e19
            | exact resolve b6e19 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e34 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X1) X1) := by
            intro X0 X1 X3
            first
            | (have i₁ := b6e13 x X1 X3
               have i₂ := b6e13 x X1 X0
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e38 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b6e13 X0 y x
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e13
            | exact resolve b6e13 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e52 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e13 X0 X0 X0
               have i₂ := b6e18 X0 X1
               grind)
            | (have i₁ := b6e13 X0 X1 X2
               have i₂ := b6e18 X0 (M.op X2 X1)
               grind)
            | exact superpose b6e18 b6e13
            | (have j1 := b6e18 X2 X0
               grind)
            | exact resolve b6e13 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e56 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b6e23
               have i₂ := b6e18 (σ x) X0
               grind)
            | (have i₁ := b6e23
               have i₂ := b6e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b6e18 b6e23
            | (have j1 := b6e18 (σ x) X0
               grind)
            | (have r₁ := b6e23
               have r₂ := b6e18 (σ x) (σ y)
               grind)
            | exact resolve b6e23 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e60 : ∀ X1 : G, (M.op y y) = (M.op (M.op X1 y) y) := by
            intro X1
            first
            | (have i₁ := b6e13 x y X1
               have i₂ := b6e38 x
               grind)
            | exact superpose b6e38 b6e13
            | exact resolve b6e13 b6e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e62 : ∀ X0 : G, (M.op y y) ≠ (M.op y y) ∨ (k X0 (M.op y y)) = X0 := by
            intro X0
            first
            | (have i₁ := b6e16 X0 (M.op y y)
               have i₂ := b6e38 X0
               grind)
            | exact superpose b6e38 b6e16
            | (have j0 := b6e16 X0 (M.op y y)
               grind)
            | (have r₁ := b6e16 X0 (M.op y y)
               have r₂ := b6e38 X0
               grind)
            | exact resolve b6e16 b6e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e66 : ∀ X0 : G, (k X0 (M.op y y)) = X0 := by
            intro X0
            first
            | (have j0 := b6e62 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e62
          have b6e72 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b6e73 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b6e72 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e72
          have b6e103 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b6e14 (k (τ X0) X1)
               have i₂ := b6e31 X0 X1
               grind)
            | exact superpose b6e31 b6e14
            | exact resolve b6e14 b6e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e31
          have b6e118 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e14 (k X0 (τ X1))
               have i₂ := b6e32 X1 X0
               grind)
            | exact superpose b6e32 b6e14
            | exact resolve b6e14 b6e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e32
          have b6e1049 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b6e56 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e56
          have b6e1050 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b6e1049
               have r₂ := b6e22
               grind)
            | exact resolve b6e1049 b6e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1049
          have b6e1051 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b6e1050
               have i₂ := b6e19 x y
               grind)
            | exact superpose b6e19 b6e1050
            | exact resolve b6e1050 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1050
          have b6e1052 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b6e1051
               have i₂ := b6e30
               grind)
            | exact superpose b6e30 b6e1051
            | exact resolve b6e1051 b6e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e30 b6e1051
          have b6e1055 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b6e22
               have i₂ := b6e1052
               grind)
            | exact superpose b6e1052 b6e22
            | exact resolve b6e22 b6e1052
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e1060 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e34 X0 (σ y) (σ x)
               have i₂ := b6e1052
               grind)
            | exact superpose b6e1052 b6e34
            | exact resolve b6e34 b6e1052
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e34
          have b6e1069 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e1060 X0
               have i₂ := b6e1052
               grind)
            | exact superpose b6e1052 b6e1060
            | exact resolve b6e1060 b6e1052
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1052 b6e1060
          have b6e1133 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b6e73 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e1134 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b6e73 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e73
          have b6e1137 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b6e1134 X0 X1
               have j1 := b6e52 X1 X1 X0
               grind)
            | (have r₁ := b6e1134 x X0
               have r₂ := b6e52 X0 x x
               grind)
            | (have r₁ := b6e1134 X0 X1
               have r₂ := b6e52 X0 X1 X1
               grind)
            | exact resolve b6e1134 b6e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e52 b6e1134
          have b6e2009 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e103 X0 X1
               have i₂ := b6e1137 X0 (σ X1)
               grind)
            | exact superpose b6e1137 b6e103
            | (have j1 := b6e1137 X0 (σ X1)
               grind)
            | exact resolve b6e103 b6e1137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e103
          have b6e2025 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b6e118 X0 X1
               have i₂ := b6e1137 (σ X0) X1
               grind)
            | exact superpose b6e1137 b6e118
            | (have j1 := b6e1137 (σ X0) X1
               grind)
            | exact resolve b6e118 b6e1137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e118
          have b6e18118 : ∀ X0 : G, (M.op y y) ≠ (M.op (M.op y y) X0) ∨ (M.op y y) = (k (M.op y y) X0) ∨ (M.op (M.op y y) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b6e1133 (M.op y y) X0
               have i₂ := b6e38 X0
               grind)
            | exact superpose b6e38 b6e1133
            | (have j0 := b6e1133 (M.op y y) X0
               grind)
            | exact resolve b6e1133 b6e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1133
          have b6e18181 : ∀ X0 : G, (M.op y y) ≠ (M.op (M.op y y) X0) ∨ (M.op y y) = (k (M.op y y) X0) := by
            intro X0
            first
            | (have j0 := b6e18118 X0
               have j1 := b6e16 (M.op y y) X0
               grind)
            | (have r₁ := b6e18118 x
               have r₂ := b6e16 (M.op y y) x
               grind)
            | exact resolve b6e18118 b6e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e18118
          have b6e466432 : ∀ X0 : G, (τ (σ x)) = (k (τ (M.op X0 (σ y))) y) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b6e2009 (M.op X0 (σ y)) y
               have i₂ := b6e1069 X0
               grind)
            | exact superpose b6e1069 b6e2009
            | exact resolve b6e2009 b6e1069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1069 b6e2009
          have b6e466542 : ∀ X0 : G, (τ (σ x)) = (k (τ (M.op X0 (σ y))) y) := by
            intro X0
            first
            | (have j0 := b6e466432 X0
               grind)
            | (have r₁ := b6e466432 X0
               have r₂ := b6e1055
               grind)
            | exact resolve b6e466432 b6e1055
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e466432
          have b6e466560 : ∀ X0 : G, x = (k (τ (M.op X0 (σ y))) y) := by
            intro X0
            first
            | (have i₁ := b6e466542 X0
               have i₂ := b6e14 x
               grind)
            | exact superpose b6e14 b6e466542
            | exact resolve b6e466542 b6e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e466542
          have b6e466684 : ∀ X0 : G, x = (k (k X0 (τ (σ y))) y) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e466560 (σ X0)
               have i₂ := b6e2025 X0 (σ y)
               grind)
            | exact superpose b6e2025 b6e466560
            | (have j1 := b6e2025 X0 (σ y)
               grind)
            | exact resolve b6e466560 b6e2025
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e2025
          have b6e466708 : ∀ X0 : G, x = (k (k X0 y) y) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e466684 X0
               have i₂ := b6e14 y
               grind)
            | exact superpose b6e14 b6e466684
            | (have j0 := b6e466684 X0
               grind)
            | exact resolve b6e466684 b6e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e466684
          have b6e552621 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (k (M.op y y) y) := by
            first
            | (have i₁ := b6e18181 y
               have i₂ := b6e60 y
               grind)
            | exact superpose b6e60 b6e18181
            | (have j0 := b6e18181 y
               grind)
            | (have r₁ := b6e18181 y
               have r₂ := b6e60 y
               grind)
            | exact resolve b6e18181 b6e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e18181
          have b6e552753 : (M.op y y) = (k (M.op y y) y) := by grind
          clear b6e552621
          have b6e552782 : x = (k (M.op y y) y) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
            first
            | (have i₁ := b6e466708 (M.op y y)
               have i₂ := b6e552753
               grind)
            | exact superpose b6e552753 b6e466708
            | (have j0 := b6e466708 (M.op y y)
               grind)
            | exact resolve b6e466708 b6e552753
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e466708
          have b6e552799 : (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b6e552782
               have i₂ := b6e552753
               grind)
            | exact superpose b6e552753 b6e552782
            | exact resolve b6e552782 b6e552753
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e552753 b6e552782
          have b6e574735 : x = (k (τ (σ y)) y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b6e466560 (σ (M.op y y))
               have i₂ := b6e552799
               grind)
            | exact superpose b6e552799 b6e466560
            | exact resolve b6e466560 b6e552799
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e466560 b6e552799
          have b6e574836 : x = (k y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b6e574735
               have i₂ := b6e14 y
               grind)
            | exact superpose b6e14 b6e574735
            | exact resolve b6e574735 b6e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e574735
          have b6e576549 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b6e1137 y y
               have i₂ := b6e574836
               grind)
            | exact superpose b6e574836 b6e1137
            | (have j0 := b6e1137 y y
               grind)
            | exact resolve b6e1137 b6e574836
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1137
          have b6e576559 : y = (M.op y y) ∨ x = (M.op y y) := by grind
          clear b6e576549
          have b6e577997 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b6e38 X0
               have i₂ := b6e576559
               grind)
            | exact superpose b6e576559 b6e38
            | exact resolve b6e38 b6e576559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e38
          have b6e578360 : x ≠ y ∨ x = (M.op y y) := by grind
          clear b6e576559
          have b6e581654 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b6e60 y
               have i₂ := b6e577997 X0
               grind)
            | exact superpose b6e577997 b6e60
            | (have j1 := b6e577997 X0
               grind)
            | exact resolve b6e60 b6e577997
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e60 b6e577997
          have b6e582226 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b6e581654 X0
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e581654
            | (have j0 := b6e581654 X0
               grind)
            | exact resolve b6e581654 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e581654
          have b6e584941 : ∀ X0 : G, (k X0 y) = X0 ∨ x = y := by
            intro X0
            first
            | (have i₁ := b6e66 X0
               have i₂ := b6e582226 y
               grind)
            | exact superpose b6e582226 b6e66
            | exact resolve b6e66 b6e582226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e66
          have b6e586580 : x = y ∨ x = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b6e574836
               have i₂ := b6e584941 y
               grind)
            | exact superpose b6e584941 b6e574836
            | exact resolve b6e574836 b6e584941
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e574836 b6e584941
          have b6e586581 : x = y ∨ x = (M.op y y) := by grind
          clear b6e586580
          have b6e586588 : x = (M.op y y) := by
            first
            | (have r₁ := b6e586581
               have r₂ := b6e578360
               grind)
            | exact resolve b6e586581 b6e578360
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e578360 b6e586581
          have b6e587698 : x = y ∨ x = y := by
            first
            | (have i₁ := b6e582226 y
               have i₂ := b6e586588
               grind)
            | exact superpose b6e586588 b6e582226
            | exact resolve b6e582226 b6e586588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e582226 b6e586588
          have b6e588071 : x = y := by grind
          clear b6e587698
          have b6e590295 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b6e1055
               have i₂ := b6e588071
               grind)
            | exact superpose b6e588071 b6e1055
            | exact resolve b6e1055 b6e588071
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1055 b6e588071
          have b6e590382 : False := by grind
          exact b6e590382
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
              intro X0 X1 X2
              grind
            have b7e22 : y = (M.op x y) := by grind
            have b7e25 : x ≠ (M.op y x) := by grind
            have b7e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e38 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y y)) := by
              intro X0
              first
              | (have i₁ := b7e14 X0 y x
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e14
              | exact resolve b7e14 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e39 : ∀ X0 : G, (M.op x y) = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b7e14 X0 y y
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e14
              | exact resolve b7e14 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e46 : ∀ X0 : G, y = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b7e39 X0
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e39
              | exact resolve b7e39 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e39
            have b7e47 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b7e38 X0
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e38
              | exact resolve b7e38 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e38
            have b7e48 : x = y := by
              first
              | (have i₁ := b7e47 x
                 have i₂ := b7e46 x
                 grind)
              | exact superpose b7e46 b7e47
              | exact resolve b7e47 b7e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e46 b7e47
            have b7e52 : y ≠ (M.op y y) := by
              first
              | (have i₁ := b7e25
                 have i₂ := b7e48
                 grind)
              | exact superpose b7e48 b7e25
              | exact resolve b7e25 b7e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e56 : x ≠ y := by
              first
              | (have i₁ := b7e52
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e52
              | exact resolve b7e52 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e52
            have b7e57 : False := by grind
            exact b7e57
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
              intro X0 X1 X2
              grind
            have b8e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b8e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : y = (M.op x y) := by grind
            have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
            have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b8e25 : x ≠ (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e29 : y ≠ y ∨ x = (k x y) := by
              first
              | (have i₁ := b8e17 x y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e17
              | (have j0 := b8e17 x y
                 grind)
              | (have r₁ := b8e17 x y
                 have r₂ := b8e22
                 grind)
              | exact resolve b8e17 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e30 : x = (k x y) := by grind
            clear b8e29
            have b8e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b8e20 X1 (τ X0)
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e20
              | exact resolve b8e20 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X1 X1)) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e14 X2 (M.op X1 X1) X3
                 have i₂ := b8e14 (M.op X1 X1) X1 X0
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e43 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14 X0 X1 x
                 have i₂ := b8e14 X2 X1 x
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b8e20 X0 X1
                 have i₂ := b8e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b8e19 b8e20
              | (have j1 := b8e19 (σ X0) (σ X1)
                 grind)
              | exact resolve b8e20 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e66 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X2 X0) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14 X0 X0 X0
                 have i₂ := b8e19 X0 X1
                 grind)
              | (have i₁ := b8e14 X0 X1 X2
                 have i₂ := b8e19 X0 (M.op X2 X1)
                 grind)
              | exact superpose b8e19 b8e14
              | (have j1 := b8e19 X2 X0
                 grind)
              | exact resolve b8e14 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e71 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b8e24
                 have i₂ := b8e19 (σ x) X0
                 grind)
              | (have i₁ := b8e24
                 have i₂ := b8e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b8e19 b8e24
              | (have j1 := b8e19 (σ x) X0
                 grind)
              | (have r₁ := b8e24
                 have r₂ := b8e19 (σ x) (σ y)
                 grind)
              | exact resolve b8e24 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e95 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b8e15 (k X0 (τ X1))
                 have i₂ := b8e32 X1 X0
                 grind)
              | exact superpose b8e32 b8e15
              | exact resolve b8e15 b8e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e32
            have b8e539 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e43 X3 X2 (M.op x (M.op X2 X2))
                 have i₂ := b8e37 X1 X2 X0 x
                 grind)
              | exact superpose b8e37 b8e43
              | exact resolve b8e43 b8e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e43
            have b8e557 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) X1) ≠ (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X1)) ∨ (k X2 (M.op (M.op X3 X1) X1)) = X2 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e17 X2 (M.op (M.op X3 X1) X1)
                 have i₂ := b8e37 X3 X1 X2 X0
                 grind)
              | exact superpose b8e37 b8e17
              | (have j0 := b8e17 X2 (M.op (M.op X3 X1) X1)
                 grind)
              | exact resolve b8e17 b8e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e37
            have b8e570 : ∀ X1 X2 X3 : G, (k X2 (M.op (M.op X3 X1) X1)) = X2 := by
              intro X1 X2 X3
              first
              | (have j0 := b8e557 x X1 X2 X3
                 grind)
              | (have r₁ := b8e557 x X1 X2 X2
                 have r₂ := b8e14 (M.op x (M.op X1 X1)) X1 X2
                 grind)
              | exact resolve b8e557 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e557
            have b8e927 : ∀ X0 : G, y = (M.op X0 x) ∨ (M.op y x) = (k y x) ∨ x = (M.op y x) := by
              intro X0
              first
              | (have i₁ := b8e22
                 have i₂ := b8e66 x X0 y
                 grind)
              | (have i₁ := b8e22
                 have i₂ := b8e66 y x x
                 grind)
              | exact superpose b8e66 b8e22
              | (have j1 := b8e66 x x y
                 grind)
              | exact resolve b8e22 b8e66
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e66
            have b8e940 : ∀ X0 : G, y = (M.op X0 x) ∨ (M.op y x) = (k y x) := by
              intro X0
              first
              | (have j0 := b8e927 X0
                 grind)
              | (have r₁ := b8e927 X0
                 have r₂ := b8e25
                 grind)
              | exact resolve b8e927 b8e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e927
            have b8e996 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have j0 := b8e71 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e71
            have b8e997 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b8e996
                 have r₂ := b8e23
                 grind)
              | exact resolve b8e996 b8e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e996
            have b8e998 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b8e997
                 have i₂ := b8e20 x y
                 grind)
              | exact superpose b8e20 b8e997
              | exact resolve b8e997 b8e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e997
            have b8e999 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b8e998
                 have i₂ := b8e30
                 grind)
              | exact superpose b8e30 b8e998
              | exact resolve b8e998 b8e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e30 b8e998
            have b8e1012 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 := by
              intro X0
              first
              | (have i₁ := b8e570 (σ y) X0 (σ x)
                 have i₂ := b8e999
                 grind)
              | exact superpose b8e999 b8e570
              | exact resolve b8e570 b8e999
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e570
            have b8e1015 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
              intro X0
              first
              | (have i₁ := b8e1012 X0
                 have i₂ := b8e999
                 grind)
              | exact superpose b8e999 b8e1012
              | exact resolve b8e1012 b8e999
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e999 b8e1012
            have b8e1110 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) := by
              intro X0
              first
              | (have i₁ := b8e95 X0 (σ x)
                 have i₂ := b8e1015 (σ X0)
                 grind)
              | exact superpose b8e1015 b8e95
              | exact resolve b8e95 b8e1015
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1015
            have b8e1113 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
              intro X0
              first
              | (have i₁ := b8e1110 X0
                 have i₂ := b8e15 x
                 grind)
              | exact superpose b8e15 b8e1110
              | exact resolve b8e1110 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1110
            have b8e1115 : ∀ X0 : G, (k X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b8e1113 X0
                 have i₂ := b8e15 X0
                 grind)
              | exact superpose b8e15 b8e1113
              | exact resolve b8e1113 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1113
            have b8e1303 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ x)) := by
              intro X0
              first
              | (have i₁ := b8e95 X0 x
                 have i₂ := b8e1115 (σ X0)
                 grind)
              | exact superpose b8e1115 b8e95
              | exact resolve b8e95 b8e1115
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e95
            have b8e1306 : ∀ X0 : G, (k X0 (τ x)) = X0 := by
              intro X0
              first
              | (have i₁ := b8e1303 X0
                 have i₂ := b8e15 X0
                 grind)
              | exact superpose b8e15 b8e1303
              | exact resolve b8e1303 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1303
            have b8e1539 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b8e63 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e63
            have b8e1541 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b8e1539 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1539
            have b8e1949 : ∀ X0 : G, y = (M.op y x) ∨ y = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b8e1115 y
                 have i₂ := b8e940 X0
                 grind)
              | exact superpose b8e940 b8e1115
              | (have j1 := b8e940 y
                 grind)
              | exact resolve b8e1115 b8e940
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e940 b8e1115
            have b8e5374 : y ≠ y ∨ y = (M.op y x) := by
              first
              | (have j0 := b8e1949 y
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1949
            have b8e5375 : y = (M.op y x) := by grind
            clear b8e5374
            have b8e5777 : x ≠ y := by
              first
              | (have i₁ := b8e25
                 have i₂ := b8e5375
                 grind)
              | exact superpose b8e5375 b8e25
              | exact resolve b8e25 b8e5375
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e5778 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op x x)) := by
              intro X0
              first
              | (have i₁ := b8e14 X0 x y
                 have i₂ := b8e5375
                 grind)
              | exact superpose b8e5375 b8e14
              | exact resolve b8e14 b8e5375
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e5805 : ∀ X0 : G, y = (M.op X0 (M.op x x)) := by
              intro X0
              first
              | (have i₁ := b8e5778 X0
                 have i₂ := b8e5375
                 grind)
              | exact superpose b8e5375 b8e5778
              | exact resolve b8e5778 b8e5375
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e5375 b8e5778
            have b8e7498 : (σ (τ x)) ≠ (σ (τ x)) ∨ (σ (τ x)) = (M.op (σ (τ x)) (σ (τ x))) := by
              first
              | (have i₁ := b8e1541 (τ x)
                 have i₂ := b8e1306 (τ x)
                 grind)
              | exact superpose b8e1306 b8e1541
              | (have j0 := b8e1541 (τ x)
                 grind)
              | exact resolve b8e1541 b8e1306
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1306 b8e1541
            have b8e7515 : (σ (τ x)) = (M.op (σ (τ x)) (σ (τ x))) := by grind
            clear b8e7498
            have b8e7543 : x = (M.op x x) := by
              first
              | (have i₁ := b8e7515
                 have i₂ := b8e16 x
                 grind)
              | exact superpose b8e16 b8e7515
              | exact resolve b8e7515 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e7515
            have b8e7588 : ∀ X0 : G, (M.op x x) = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b8e14 X0 x x
                 have i₂ := b8e7543
                 grind)
              | exact superpose b8e7543 b8e14
              | exact resolve b8e14 b8e7543
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e7608 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 (M.op x x)) := by
              intro X0 X1
              first
              | (have i₁ := b8e539 X0 x x x
                 have i₂ := b8e7543
                 grind)
              | exact superpose b8e7543 b8e539
              | exact resolve b8e539 b8e7543
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e539
            have b8e7617 : ∀ X0 : G, y = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b8e7608 X0 x
                 have i₂ := b8e5805 x
                 grind)
              | exact superpose b8e5805 b8e7608
              | exact resolve b8e7608 b8e5805
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e5805 b8e7608
            have b8e7625 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b8e7588 X0
                 have i₂ := b8e7543
                 grind)
              | exact superpose b8e7543 b8e7588
              | exact resolve b8e7588 b8e7543
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e7543 b8e7588
            have b8e7634 : x = y := by
              first
              | (have i₁ := b8e7625 x
                 have i₂ := b8e7617 x
                 grind)
              | exact superpose b8e7617 b8e7625
              | exact resolve b8e7625 b8e7617
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e7617 b8e7625
            have b8e7639 : False := by grind
            exact b8e7639
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y x) (x) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
            intro X0 X1 X2
            grind
          have b9e21 : y ≠ (M.op x y) := by grind
          have b9e22 : y = (M.op x x) := by grind
          have b9e24 : x = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e49 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b9e13 X0 x y
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e13
            | exact resolve b9e13 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e54 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b9e49 X0
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e49
            | exact resolve b9e49 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e49
          have b9e62 : y ≠ y := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e54 x
               grind)
            | exact superpose b9e54 b9e21
            | (have r₁ := b9e21
               have r₂ := b9e54 x
               grind)
            | exact resolve b9e21 b9e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e54
          have b9e63 : False := by grind
          exact b9e63
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e22 : y ≠ (M.op x y) := by grind
            have b10e23 : y = (M.op x x) := by grind
            have b10e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
            have b10e25 : x ≠ (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e31 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b10e17 (σ x) (σ y)
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e17
              | (have j0 := b10e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b10e17 (σ x) (σ y)
                 have r₂ := b10e24
                 grind)
              | exact resolve b10e17 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e32 : (σ x) = (k (σ x) (σ y)) := by grind
            clear b10e31
            have b10e33 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b10e32
                 have i₂ := b10e20 x y
                 grind)
              | exact superpose b10e20 b10e32
              | exact resolve b10e32 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e32
            have b10e38 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b10e15 (k x y)
                 have i₂ := b10e33
                 grind)
              | exact superpose b10e33 b10e15
              | exact resolve b10e15 b10e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e33
            have b10e39 : x = (k x y) := by
              first
              | (have i₁ := b10e38
                 have i₂ := b10e15 x
                 grind)
              | exact superpose b10e15 b10e38
              | exact resolve b10e38 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e38
            have b10e88 : (M.op y x) = (k x y) ∨ y = (M.op x y) := by grind
            have b10e92 : (M.op y x) = (k x y) := by
              first
              | (have r₁ := b10e88
                 have r₂ := b10e22
                 grind)
              | exact resolve b10e88 b10e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e88
            have b10e94 : x = (M.op y x) := by
              first
              | (have i₁ := b10e92
                 have i₂ := b10e39
                 grind)
              | exact superpose b10e39 b10e92
              | exact resolve b10e92 b10e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e39 b10e92
            have b10e95 : False := by grind
            exact b10e95
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : y ≠ (M.op x y) := by grind
            have b11e23 : y = (M.op x x) := by grind
            have b11e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
            have b11e25 : x ≠ (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e30 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b11e17 (σ x) (σ y)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e17
              | (have j0 := b11e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b11e17 (σ x) (σ y)
                 have r₂ := b11e24
                 grind)
              | exact resolve b11e17 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e31 : (σ x) = (k (σ x) (σ y)) := by grind
            clear b11e30
            have b11e32 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b11e31
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e31
              | exact resolve b11e31 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e31
            have b11e37 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 (k x y)
                 have i₂ := b11e32
                 grind)
              | exact superpose b11e32 b11e15
              | exact resolve b11e15 b11e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e32
            have b11e38 : x = (k x y) := by
              first
              | (have i₁ := b11e37
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e37
              | exact resolve b11e37 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e37
            have b11e78 : (M.op y x) = (k x y) ∨ y = (M.op x y) := by grind
            have b11e80 : (M.op y x) = (k x y) := by
              first
              | (have r₁ := b11e78
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e78 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e78
            have b11e81 : x = (M.op y x) := by
              first
              | (have i₁ := b11e80
                 have i₂ := b11e38
                 grind)
              | exact superpose b11e38 b11e80
              | exact resolve b11e80 b11e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e38 b11e80
            have b11e82 : False := by grind
            exact b11e82
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op y x) (x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
              intro X0 X1 X2
              grind
            have b12e22 : y ≠ (M.op x y) := by grind
            have b12e23 : y = (M.op x x) := by grind
            have b12e26 : x = (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e48 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op x x)) := by
              intro X0
              first
              | (have i₁ := b12e14 X0 x y
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e14
              | exact resolve b12e14 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e53 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b12e48 X0
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e48
              | exact resolve b12e48 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e48
            have b12e60 : y ≠ y := by
              first
              | (have i₁ := b12e22
                 have i₂ := b12e53 x
                 grind)
              | exact superpose b12e53 b12e22
              | (have r₁ := b12e22
                 have r₂ := b12e53 x
                 grind)
              | exact resolve b12e22 b12e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e53
            have b12e61 : False := by grind
            exact b12e61
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
                intro X0 X1 X2
                grind
              have b13e23 : y ≠ (M.op x y) := by grind
              have b13e24 : y = (M.op x x) := by grind
              have b13e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e46 : ∀ X0 : G, (M.op x y) = (M.op X0 x) := by
                intro X0
                first
                | (have i₁ := b13e15 X0 y y
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e15
                | exact resolve b13e15 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e55 : ∀ X0 : G, y ≠ (M.op X0 x) := by
                intro X0
                first
                | (have i₁ := b13e23
                   have i₂ := b13e46 X0
                   grind)
                | exact superpose b13e46 b13e23
                | exact resolve b13e23 b13e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e46
              have b13e80 : y ≠ y := by
                first
                | (have i₁ := b13e55 x
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e55
                | (have r₁ := b13e55 x
                   have r₂ := b13e24
                   grind)
                | exact resolve b13e55 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e55
              have b13e81 : False := by grind
              exact b13e81
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
                intro X0 X1 X2
                grind
              have b14e19 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e23 : y ≠ (M.op x y) := by grind
              have b14e24 : y = (M.op x x) := by grind
              have b14e25 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e46 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (σ x)) := by
                intro X0
                first
                | (have i₁ := b14e15 X0 (σ x) (σ x)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e15
                | exact resolve b14e15 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e47 : ∀ X0 : G, (M.op y x) = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e15 X0 x x
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e52 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b14e47 X1
                   have i₂ := b14e47 X0
                   grind)
                | exact superpose b14e47 b14e47
                | exact resolve b14e47 b14e47
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e86 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
              have b14e87 : (M.op y x) = (k x y) ∨ y = (M.op x y) := by grind
              have b14e90 : (M.op y x) = (k x y) := by
                first
                | (have r₁ := b14e87
                   have r₂ := b14e23
                   grind)
                | exact resolve b14e87 b14e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e87
              have b14e91 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b14e86
                   have r₂ := b14e25
                   grind)
                | exact resolve b14e86 b14e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e86
              have b14e92 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b14e91
                   have i₂ := b14e21 x y
                   grind)
                | exact superpose b14e21 b14e91
                | exact resolve b14e91 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e91
              have b14e93 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
                first
                | (have i₁ := b14e92
                   have i₂ := b14e90
                   grind)
                | exact superpose b14e90 b14e92
                | exact resolve b14e92 b14e90
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e90 b14e92
              have b14e182 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
                intro X0 X1
                first
                | (have i₁ := b14e46 X0
                   have i₂ := b14e46 X1
                   grind)
                | exact superpose b14e46 b14e46
                | exact resolve b14e46 b14e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e212 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (M.op y x)) := by
                intro X0
                first
                | (have i₁ := b14e46 X0
                   have i₂ := b14e93
                   grind)
                | exact superpose b14e93 b14e46
                | exact resolve b14e46 b14e93
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e46 b14e93
              have b14e1020 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b14e22
                   have i₂ := b14e182 (σ x) X0
                   grind)
                | (have i₁ := b14e22
                   have i₂ := b14e182 X0 (σ x)
                   grind)
                | exact superpose b14e182 b14e22
                | exact resolve b14e22 b14e182
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e182
              have b14e1800 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (σ (M.op X0 y)) := by
                intro X0 X1
                first
                | (have i₁ := b14e212 X1
                   have i₂ := b14e47 X0
                   grind)
                | exact superpose b14e47 b14e212
                | exact resolve b14e212 b14e47
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e47 b14e212
              have b14e3165 : ∀ X0 X1 : G, (M.op X1 (σ y)) ≠ (σ (M.op X0 y)) := by
                intro X0 X1
                first
                | (have i₁ := b14e1020 X1
                   have i₂ := b14e52 x X0
                   grind)
                | (have i₁ := b14e1020 X1
                   have i₂ := b14e52 X0 x
                   grind)
                | exact superpose b14e52 b14e1020
                | exact resolve b14e1020 b14e52
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e52 b14e1020
              have b14e3191 : False := by grind
              exact b14e3191
        · rcases eq_or_ne (M.op y x) (x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
              intro X0 X1 X2
              grind
            have b15e22 : y ≠ (M.op x y) := by grind
            have b15e23 : y = (M.op x x) := by grind
            have b15e26 : x = (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e42 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op x x)) := by
              intro X0
              first
              | (have i₁ := b15e14 X0 x y
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e14
              | exact resolve b15e14 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e49 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b15e42 X0
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e42
              | exact resolve b15e42 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e42
            have b15e56 : y ≠ y := by
              first
              | (have i₁ := b15e22
                 have i₂ := b15e49 x
                 grind)
              | exact superpose b15e49 b15e22
              | (have r₁ := b15e22
                 have r₂ := b15e49 x
                 grind)
              | exact resolve b15e22 b15e49
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e49
            have b15e57 : False := by grind
            exact b15e57
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
                intro X0 X1 X2
                grind
              have b16e23 : y ≠ (M.op x y) := by grind
              have b16e24 : y = (M.op x x) := by grind
              have b16e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e42 : ∀ X0 : G, (M.op x y) = (M.op X0 x) := by
                intro X0
                first
                | (have i₁ := b16e15 X0 y y
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e15
                | exact resolve b16e15 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e51 : ∀ X0 : G, y ≠ (M.op X0 x) := by
                intro X0
                first
                | (have i₁ := b16e23
                   have i₂ := b16e42 X0
                   grind)
                | exact superpose b16e42 b16e23
                | exact resolve b16e23 b16e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e42
              have b16e75 : y ≠ y := by
                first
                | (have i₁ := b16e51 x
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e51
                | (have r₁ := b16e51 x
                   have r₂ := b16e24
                   grind)
                | exact resolve b16e51 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e51
              have b16e76 : False := by grind
              exact b16e76
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
                intro X0 X1 X2
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b17e23 : y ≠ (M.op x y) := by grind
              have b17e24 : y = (M.op x x) := by grind
              have b17e25 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
              have b17e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e41 : ∀ X0 : G, (M.op y x) = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b17e15 X0 x x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b17e21 X0 X1
                   have i₂ := b17e20 (σ X0) (σ X1)
                   grind)
                | exact superpose b17e20 b17e21
                | (have j1 := b17e20 (σ X0) (σ X1)
                   grind)
                | exact resolve b17e21 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e81 : (M.op y x) = (k x y) ∨ y = (M.op x y) := by grind
              have b17e84 : (M.op y x) = (k x y) := by
                first
                | (have r₁ := b17e81
                   have r₂ := b17e23
                   grind)
                | exact resolve b17e81 b17e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e81
              have b17e2270 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b17e22
                   have i₂ := b17e67 x y
                   grind)
                | exact superpose b17e67 b17e22
                | (have j1 := b17e67 x y
                   grind)
                | exact resolve b17e22 b17e67
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e67
              have b17e2358 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b17e2270
                   have r₂ := b17e26
                   grind)
                | exact resolve b17e2270 b17e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e2270
              have b17e2366 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have r₁ := b17e2358
                   have r₂ := b17e25
                   grind)
                | exact resolve b17e2358 b17e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e2358
              have b17e2368 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
                first
                | (have i₁ := b17e2366
                   have i₂ := b17e84
                   grind)
                | exact superpose b17e84 b17e2366
                | exact resolve b17e2366 b17e84
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e84 b17e2366
              have b17e2369 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op X0 y)) := by
                intro X0
                first
                | (have i₁ := b17e2368
                   have i₂ := b17e41 X0
                   grind)
                | exact superpose b17e41 b17e2368
                | exact resolve b17e2368 b17e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e41 b17e2368
              have b17e2443 : False := by grind
              exact b17e2443
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y x) (x) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
            intro X0 X1 X2
            grind
          have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b18e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b18e21 : y ≠ (M.op x y) := by grind
          have b18e22 : y ≠ (M.op x x) := by grind
          have b18e23 : (σ y) = (M.op (σ x) (σ y)) := by grind
          have b18e24 : x = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e26 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b18e20
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e20
            | exact resolve b18e20 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e28 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b18e29 : (σ x) = (k (σ x) (σ y)) := by grind
          clear b18e28
          have b18e31 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b18e29
               have i₂ := b18e19 x y
               grind)
            | exact superpose b18e19 b18e29
            | exact resolve b18e29 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e29
          have b18e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b18e19 X1 (τ X0)
               have i₂ := b18e15 X0
               grind)
            | exact superpose b18e15 b18e19
            | exact resolve b18e19 b18e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e36 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b18e14 (k x y)
               have i₂ := b18e31
               grind)
            | exact superpose b18e31 b18e14
            | exact resolve b18e14 b18e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e31
          have b18e37 : x = (k x y) := by
            first
            | (have i₁ := b18e36
               have i₂ := b18e14 x
               grind)
            | exact superpose b18e14 b18e36
            | exact resolve b18e36 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e36
          have b18e41 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X1) X1) := by
            intro X0 X1 X3
            first
            | (have i₁ := b18e13 x X1 X3
               have i₂ := b18e13 x X1 X0
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e44 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e13 X2 X1 (M.op x X1)
               have i₂ := b18e13 X0 X1 x
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e45 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ y) (σ y))) := by
            intro X0
            first
            | (have i₁ := b18e13 X0 (σ y) (σ x)
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e13
            | exact resolve b18e13 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e46 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b18e13 X0 x y
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e13
            | exact resolve b18e13 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e48 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e13 X2 (M.op X1 X1) x
               have i₂ := b18e13 (M.op x (M.op X1 X1)) X1 X0
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b18e57 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b18e37
               have i₂ := b18e18 x y
               grind)
            | exact superpose b18e18 b18e37
            | (have j1 := b18e18 x y
               grind)
            | exact resolve b18e37 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e37
          have b18e60 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e13 X0 X0 X0
               have i₂ := b18e18 X0 X1
               grind)
            | (have i₁ := b18e13 X0 X1 X2
               have i₂ := b18e18 X0 (M.op X2 X1)
               grind)
            | exact superpose b18e18 b18e13
            | (have j1 := b18e18 X2 X0
               grind)
            | exact resolve b18e13 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e65 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b18e57
               have r₂ := b18e22
               grind)
            | exact resolve b18e57 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e57
          have b18e68 : x = (M.op x y) := by
            first
            | (have r₁ := b18e65
               have r₂ := b18e21
               grind)
            | exact resolve b18e65 b18e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e65
          have b18e70 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b18e26
               have i₂ := b18e68
               grind)
            | exact superpose b18e68 b18e26
            | exact resolve b18e26 b18e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e26
          have b18e71 : x ≠ y := by
            first
            | (have i₁ := b18e21
               have i₂ := b18e68
               grind)
            | exact superpose b18e68 b18e21
            | exact resolve b18e21 b18e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e72 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b18e13 X0 y x
               have i₂ := b18e68
               grind)
            | exact superpose b18e68 b18e13
            | exact resolve b18e13 b18e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e74 : ∀ X0 : G, x = (M.op X0 (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b18e72 X0
               have i₂ := b18e68
               grind)
            | exact superpose b18e68 b18e72
            | exact resolve b18e72 b18e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e72
          have b18e76 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b18e77 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b18e76 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e76
          have b18e83 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (k X0 (M.op x x)) = X0 := by
            intro X0
            first
            | (have i₁ := b18e16 X0 (M.op x x)
               have i₂ := b18e46 X0
               grind)
            | exact superpose b18e46 b18e16
            | (have j0 := b18e16 X0 (M.op x x)
               grind)
            | (have r₁ := b18e16 X0 (M.op x x)
               have r₂ := b18e46 X0
               grind)
            | exact resolve b18e16 b18e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e46
          have b18e88 : ∀ X0 : G, (k X0 (M.op x x)) = X0 := by
            intro X0
            first
            | (have j0 := b18e83 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e83
          have b18e111 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b18e14 (k X0 (τ X1))
               have i₂ := b18e33 X1 X0
               grind)
            | exact superpose b18e33 b18e14
            | exact resolve b18e14 b18e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e141 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) y) := by
            intro X0
            first
            | (have i₁ := b18e41 X0 y x
               have i₂ := b18e68
               grind)
            | exact superpose b18e68 b18e41
            | exact resolve b18e41 b18e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e41
          have b18e158 : ∀ X0 : G, x = (M.op (M.op X0 y) y) := by
            intro X0
            first
            | (have i₁ := b18e141 X0
               have i₂ := b18e68
               grind)
            | exact superpose b18e68 b18e141
            | exact resolve b18e141 b18e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e68 b18e141
          have b18e175 : ∀ X0 : G, x = (M.op X0 (M.op (M.op y y) (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b18e13 X0 (M.op y y) x
               have i₂ := b18e74 (M.op x (M.op y y))
               grind)
            | exact superpose b18e74 b18e13
            | exact resolve b18e13 b18e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e176 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b18e175 X0
               have i₂ := b18e74 (M.op y y)
               grind)
            | exact superpose b18e74 b18e175
            | exact resolve b18e175 b18e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e74 b18e175
          have b18e246 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b18e88 X0
               have i₂ := b18e176 x
               grind)
            | exact superpose b18e176 b18e88
            | exact resolve b18e88 b18e176
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e88 b18e176
          have b18e358 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k X0 (M.op (σ y) (σ y))) = X0 := by
            intro X0
            first
            | (have i₁ := b18e16 X0 (M.op (σ y) (σ y))
               have i₂ := b18e45 X0
               grind)
            | exact superpose b18e45 b18e16
            | (have j0 := b18e16 X0 (M.op (σ y) (σ y))
               grind)
            | (have r₁ := b18e16 X0 (M.op (σ y) (σ y))
               have r₂ := b18e45 X0
               grind)
            | exact resolve b18e16 b18e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e363 : ∀ X0 : G, (k X0 (M.op (σ y) (σ y))) = X0 := by
            intro X0
            first
            | (have j0 := b18e358 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e358
          have b18e1207 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b18e77 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e1208 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b18e77 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e77
          have b18e1211 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b18e1208 X0 X1
               have j1 := b18e60 X1 X1 X0
               grind)
            | (have r₁ := b18e1208 x X0
               have r₂ := b18e60 X0 x x
               grind)
            | (have r₁ := b18e1208 X0 X1
               have r₂ := b18e60 X0 X1 X1
               grind)
            | exact resolve b18e1208 b18e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e60 b18e1208
          have b18e1750 : ∀ X0 : G, (σ (k y y)) = (M.op X0 (σ (k y y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b18e45 X0
               have i₂ := b18e56 y y
               grind)
            | exact superpose b18e56 b18e45
            | (have j1 := b18e56 y y
               grind)
            | exact resolve b18e45 b18e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e45
          have b18e1751 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ X0)) (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e13 X1 (σ X0) X2
               have i₂ := b18e56 X0 X0
               grind)
            | exact superpose b18e56 b18e13
            | (have j1 := b18e56 X0 X0
               grind)
            | exact resolve b18e13 b18e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e1756 : ∀ X0 X1 X2 : G, (M.op X1 (σ (k X0 X0))) = (M.op (M.op X2 (σ (k X0 X0))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e44 X0 (σ X1) X2
               have i₂ := b18e56 X1 X1
               grind)
            | exact superpose b18e56 b18e44
            | (have j1 := b18e56 X0 X0
               grind)
            | exact resolve b18e44 b18e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e44
          have b18e1811 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b18e56 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e1813 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b18e1811 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1811
          have b18e1820 : ∀ X0 X1 X2 : G, (M.op X1 (σ (k X0 X0))) = (M.op (M.op X2 (σ (k X0 X0))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have j0 := b18e1756 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1756
          have b18e1825 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ X0)) (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have j0 := b18e1751 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1751
          have b18e1826 : ∀ X0 : G, (σ (k y y)) = (M.op X0 (σ (k y y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have j0 := b18e1750 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1750
          have b18e1869 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ y) (σ y)))) := by
            intro X0
            first
            | (have i₁ := b18e111 X0 (M.op (σ y) (σ y))
               have i₂ := b18e363 (σ X0)
               grind)
            | exact superpose b18e363 b18e111
            | exact resolve b18e111 b18e363
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e111 b18e363
          have b18e1891 : ∀ X0 : G, (k X0 (τ (M.op (σ y) (σ y)))) = X0 := by
            intro X0
            first
            | (have i₁ := b18e1869 X0
               have i₂ := b18e14 X0
               grind)
            | exact superpose b18e14 b18e1869
            | exact resolve b18e1869 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1869
          have b18e3289 : ∀ X0 : G, (k X0 (τ (σ (k y y)))) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b18e1891 X0
               have i₂ := b18e56 y y
               grind)
            | exact superpose b18e56 b18e1891
            | (have j1 := b18e56 y y
               grind)
            | exact resolve b18e1891 b18e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e56
          have b18e3317 : ∀ X0 : G, (k X0 (τ (σ (k y y)))) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have j0 := b18e3289 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3289
          have b18e3320 : ∀ X0 : G, (k X0 (k y y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b18e3317 X0
               have i₂ := b18e14 (k y y)
               grind)
            | exact superpose b18e14 b18e3317
            | exact resolve b18e3317 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3317
          have b18e8366 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b18e1813 x
               have i₂ := b18e246 x
               grind)
            | exact superpose b18e246 b18e1813
            | (have j0 := b18e1813 x
               grind)
            | exact resolve b18e1813 b18e246
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e246
          have b18e8371 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b18e1813 (τ X0)
               have i₂ := b18e33 X0 (τ X0)
               grind)
            | exact superpose b18e33 b18e1813
            | (have j0 := b18e1813 (τ X0)
               grind)
            | exact resolve b18e1813 b18e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1813
          have b18e8373 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b18e8366
          have b18e8407 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b18e8371 X0
               have i₂ := b18e15 X0
               grind)
            | exact superpose b18e15 b18e8371
            | (have j0 := b18e8371 X0
               grind)
            | exact resolve b18e8371 b18e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e8371
          have b18e8423 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b18e8407 X0
               have i₂ := b18e15 X0
               grind)
            | exact superpose b18e15 b18e8407
            | (have j0 := b18e8407 X0
               grind)
            | exact resolve b18e8407 b18e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e8407
          have b18e8467 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op (σ x) (σ x))) := by
            intro X0
            first
            | (have i₁ := b18e48 (σ x) (σ x) x
               have i₂ := b18e8373
               grind)
            | exact superpose b18e8373 b18e48
            | exact resolve b18e48 b18e8373
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e48
          have b18e8502 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b18e8467 X0
               have i₂ := b18e8373
               grind)
            | exact superpose b18e8373 b18e8467
            | exact resolve b18e8467 b18e8373
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e8373 b18e8467
          have b18e29769 : ∀ X0 X1 X2 : G, (M.op X2 (k (σ (τ X0)) X0)) = (M.op (M.op X1 (σ (τ X0))) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e1825 (τ X0) X2 X1
               have i₂ := b18e33 X0 (τ X0)
               grind)
            | exact superpose b18e33 b18e1825
            | (have j0 := b18e1825 (τ X0) X1 X2
               grind)
            | exact resolve b18e1825 b18e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e33 b18e1825
          have b18e30107 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X0) = (M.op X2 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e29769 X0 X1 X2
               have i₂ := b18e15 X0
               grind)
            | exact superpose b18e15 b18e29769
            | (have j0 := b18e29769 X0 X1 X2
               grind)
            | exact resolve b18e29769 b18e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e29769
          have b18e30144 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X0) = (M.op X2 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e30107 X0 X1 X2
               have i₂ := b18e15 X0
               grind)
            | exact superpose b18e15 b18e30107
            | (have j0 := b18e30107 X0 X1 X2
               grind)
            | exact resolve b18e30107 b18e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e30107
          have b18e55285 : ∀ X0 : G, (M.op X0 (σ (k y y))) = (M.op (σ (k y y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b18e1820 y X0 x
               have i₂ := b18e1826 x
               grind)
            | exact superpose b18e1826 b18e1820
            | (have j0 := b18e1820 y x x
               grind)
            | exact resolve b18e1820 b18e1826
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1820 b18e1826
          have b18e55711 : ∀ X0 : G, (M.op X0 (σ (k y y))) = (M.op (σ (k y y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have j0 := b18e55285 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e55285
          have b18e356901 : (k y y) ≠ (k y y) ∨ (k y y) = (M.op (k y y) (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b18e8423 (k y y)
               have i₂ := b18e3320 (k y y)
               grind)
            | exact superpose b18e3320 b18e8423
            | (have j0 := b18e8423 (k y y)
               grind)
            | (have r₁ := b18e8423 (k y y)
               have r₂ := b18e3320 (k y y)
               grind)
            | exact resolve b18e8423 b18e3320
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3320
          have b18e356955 : (k y y) = (M.op (k y y) (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b18e356901
          have b18e460571 : ∀ X0 : G, x = (M.op X0 (k y y)) ∨ y = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b18e158 x
               have i₂ := b18e30144 y x X0
               grind)
            | exact superpose b18e30144 b18e158
            | (have j1 := b18e30144 y x x
               grind)
            | exact resolve b18e158 b18e30144
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e30144
          have b18e1397292 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (k y y) := by
            first
            | (have i₁ := b18e460571 (k y y)
               have i₂ := b18e356955
               grind)
            | exact superpose b18e356955 b18e460571
            | exact resolve b18e460571 b18e356955
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e356955 b18e460571
          have b18e1397412 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ y = (M.op y y) ∨ x = (k y y) := by
            intro X0
            first
            | (have i₁ := b18e1891 X0
               have i₂ := b18e1397292
               grind)
            | exact superpose b18e1397292 b18e1891
            | exact resolve b18e1891 b18e1397292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1891 b18e1397292
          have b18e1397426 : ∀ X0 : G, x = (k y y) ∨ (k X0 y) = X0 ∨ y = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b18e1397412 X0
               have i₂ := b18e14 y
               grind)
            | exact superpose b18e14 b18e1397412
            | exact resolve b18e1397412 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1397412
          have b18e1397430 : y ≠ y ∨ y = (M.op y y) ∨ x = (k y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b18e8423 y
               have i₂ := b18e1397426 y
               grind)
            | exact superpose b18e1397426 b18e8423
            | (have j0 := b18e8423 y
               grind)
            | (have r₁ := b18e8423 y
               have r₂ := b18e1397426 y
               grind)
            | exact resolve b18e8423 b18e1397426
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e8423 b18e1397426
          have b18e1397436 : y ≠ y ∨ y = (M.op y y) ∨ x = (k y y) := by grind
          clear b18e1397430
          have b18e1397437 : x = (k y y) ∨ y = (M.op y y) := by grind
          clear b18e1397436
          have b18e1397484 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b18e1211 y y
               have i₂ := b18e1397437
               grind)
            | exact superpose b18e1397437 b18e1211
            | (have j0 := b18e1211 y y
               grind)
            | exact resolve b18e1211 b18e1397437
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1211 b18e1397437
          have b18e1397513 : y = (M.op y y) ∨ x = (M.op y y) := by grind
          clear b18e1397484
          have b18e1397640 : x = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b18e158 y
               have i₂ := b18e1397513
               grind)
            | exact superpose b18e1397513 b18e158
            | exact resolve b18e158 b18e1397513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e158 b18e1397513
          have b18e1398000 : x = (M.op y y) := by grind
          clear b18e1397640
          have b18e1398849 : x ≠ x ∨ x = (k y y) ∨ x = y := by
            first
            | (have i₁ := b18e1207 y y
               have i₂ := b18e1398000
               grind)
            | exact superpose b18e1398000 b18e1207
            | exact resolve b18e1207 b18e1398000
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1207 b18e1398000
          have b18e1399282 : x = (k y y) ∨ x = y := by grind
          clear b18e1398849
          have b18e1399704 : x = (k y y) := by
            first
            | (have r₁ := b18e1399282
               have r₂ := b18e71
               grind)
            | exact resolve b18e1399282 b18e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e71 b18e1399282
          have b18e1402960 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b18e55711 X0
               have i₂ := b18e1399704
               grind)
            | exact superpose b18e1399704 b18e55711
            | exact resolve b18e55711 b18e1399704
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e55711
          have b18e1403202 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b18e1402960 x
               have i₂ := b18e8502 x
               grind)
            | exact superpose b18e8502 b18e1402960
            | exact resolve b18e1402960 b18e8502
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e8502 b18e1402960
          have b18e1403246 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b18e1403202
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e1403202
            | exact resolve b18e1403202 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1403202
          have b18e1403254 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have r₁ := b18e1403246
               have r₂ := b18e70
               grind)
            | exact resolve b18e1403246 b18e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1403246
          have b18e1403910 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b18e16 (σ y) (σ y)
               have i₂ := b18e1403254
               grind)
            | exact superpose b18e1403254 b18e16
            | (have j0 := b18e16 (σ y) (σ y)
               grind)
            | (have r₁ := b18e16 (σ y) (σ y)
               have r₂ := b18e1403254
               grind)
            | exact resolve b18e16 b18e1403254
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1403254
          have b18e1404209 : (σ y) = (k (σ y) (σ y)) := by grind
          clear b18e1403910
          have b18e1404233 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b18e1404209
               have i₂ := b18e19 y y
               grind)
            | exact superpose b18e19 b18e1404209
            | exact resolve b18e1404209 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1404209
          have b18e1404283 : (σ x) = (σ y) := by
            first
            | (have i₁ := b18e1404233
               have i₂ := b18e1399704
               grind)
            | exact superpose b18e1399704 b18e1404233
            | exact resolve b18e1404233 b18e1399704
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1399704 b18e1404233
          have b18e1404290 : False := by grind
          exact b18e1404290
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
              intro X0 X1 X2
              grind
            have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b19e18 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : y ≠ (M.op x y) := by grind
            have b19e23 : y ≠ (M.op x x) := by grind
            have b19e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
            have b19e25 : x ≠ (M.op y x) := by grind
            have b19e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e30 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
            have b19e31 : (σ x) = (k (σ x) (σ y)) := by grind
            clear b19e30
            have b19e32 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b19e31
                 have i₂ := b19e20 x y
                 grind)
              | exact superpose b19e20 b19e31
              | exact resolve b19e31 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e31
            have b19e37 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b19e15 (k x y)
                 have i₂ := b19e32
                 grind)
              | exact superpose b19e32 b19e15
              | exact resolve b19e15 b19e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e32
            have b19e38 : x = (k x y) := by
              first
              | (have i₁ := b19e37
                 have i₂ := b19e15 x
                 grind)
              | exact superpose b19e15 b19e37
              | exact resolve b19e37 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e37
            have b19e48 : ∀ X0 : G, (M.op x y) = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b19e14 X0 y y
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e14
              | exact resolve b19e14 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e58 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b19e38
                 have i₂ := b19e19 x y
                 grind)
              | exact superpose b19e19 b19e38
              | (have j1 := b19e19 x y
                 grind)
              | exact resolve b19e38 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e38
            have b19e65 : x = (M.op x y) ∨ y = (M.op x y) := by
              first
              | (have r₁ := b19e58
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e58 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e58
            have b19e68 : x = (M.op x y) := by
              first
              | (have r₁ := b19e65
                 have r₂ := b19e22
                 grind)
              | exact resolve b19e65 b19e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e65
            have b19e71 : x ≠ y := by
              first
              | (have i₁ := b19e22
                 have i₂ := b19e68
                 grind)
              | exact superpose b19e68 b19e22
              | exact resolve b19e22 b19e68
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e77 : (M.op x y) = (k y x) ∨ x = (M.op y x) := by grind
            have b19e79 : (M.op x y) = (k y x) := by
              first
              | (have r₁ := b19e77
                 have r₂ := b19e25
                 grind)
              | exact resolve b19e77 b19e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e77
            have b19e80 : x = (k y x) := by
              first
              | (have i₁ := b19e79
                 have i₂ := b19e68
                 grind)
              | exact superpose b19e68 b19e79
              | exact resolve b19e79 b19e68
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e79
            have b19e96 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b19e17 X0 x
                 have i₂ := b19e48 X0
                 grind)
              | exact superpose b19e48 b19e17
              | (have j0 := b19e17 X0 x
                 grind)
              | exact resolve b19e17 b19e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e48
            have b19e100 : ∀ X0 : G, (k X0 x) = X0 := by
              intro X0
              first
              | (have j0 := b19e96 X0
                 grind)
              | (have r₁ := b19e96 X0
                 have r₂ := b19e68
                 grind)
              | exact resolve b19e96 b19e68
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e68 b19e96
            have b19e121 : x = y := by
              first
              | (have i₁ := b19e80
                 have i₂ := b19e100 y
                 grind)
              | exact superpose b19e100 b19e80
              | exact resolve b19e80 b19e100
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e80 b19e100
            have b19e122 : False := by grind
            exact b19e122
          · have b20e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
              intro X0 X1 X2
              grind
            have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op x y) := by grind
            have b20e23 : y ≠ (M.op x x) := by grind
            have b20e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
            have b20e25 : x ≠ (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e29 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b20e17 (σ x) (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e17
              | (have j0 := b20e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b20e17 (σ x) (σ y)
                 have r₂ := b20e24
                 grind)
              | exact resolve b20e17 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e30 : (σ x) = (k (σ x) (σ y)) := by grind
            clear b20e29
            have b20e31 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b20e30
                 have i₂ := b20e20 x y
                 grind)
              | exact superpose b20e20 b20e30
              | exact resolve b20e30 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e30
            have b20e36 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b20e15 (k x y)
                 have i₂ := b20e31
                 grind)
              | exact superpose b20e31 b20e15
              | exact resolve b20e15 b20e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e31
            have b20e37 : x = (k x y) := by
              first
              | (have i₁ := b20e36
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e36
              | exact resolve b20e36 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e36
            have b20e55 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b20e37
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e37
              | (have j1 := b20e19 x y
                 grind)
              | exact resolve b20e37 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e37
            have b20e62 : x = (M.op x y) ∨ y = (M.op x y) := by
              first
              | (have r₁ := b20e55
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e55 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e55
            have b20e65 : x = (M.op x y) := by
              first
              | (have r₁ := b20e62
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e62 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e62
            have b20e69 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op y y)) := by
              intro X0
              first
              | (have i₁ := b20e14 X0 y x
                 have i₂ := b20e65
                 grind)
              | exact superpose b20e65 b20e14
              | exact resolve b20e14 b20e65
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e71 : ∀ X0 : G, x = (M.op X0 (M.op y y)) := by
              intro X0
              first
              | (have i₁ := b20e69 X0
                 have i₂ := b20e65
                 grind)
              | exact superpose b20e65 b20e69
              | exact resolve b20e69 b20e65
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e65 b20e69
            have b20e144 : ∀ X0 : G, x = (M.op X0 (M.op (M.op y y) (M.op y y))) := by
              intro X0
              first
              | (have i₁ := b20e14 X0 (M.op y y) x
                 have i₂ := b20e71 (M.op x (M.op y y))
                 grind)
              | exact superpose b20e71 b20e14
              | exact resolve b20e14 b20e71
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e145 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b20e144 X0
                 have i₂ := b20e71 (M.op y y)
                 grind)
              | exact superpose b20e71 b20e144
              | exact resolve b20e144 b20e71
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e71 b20e144
            have b20e211 : x ≠ x := by
              first
              | (have i₁ := b20e25
                 have i₂ := b20e145 y
                 grind)
              | exact superpose b20e145 b20e25
              | (have r₁ := b20e25
                 have r₂ := b20e145 y
                 grind)
              | exact resolve b20e25 b20e145
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e145
            have b20e212 : False := by grind
            exact b20e212
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op y x) (x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
              intro X0 X1 X2
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b21e22 : y ≠ (M.op x y) := by grind
            have b21e23 : y ≠ (M.op x x) := by grind
            have b21e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
            have b21e25 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e40 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (σ x)) := by
              intro X0
              first
              | (have i₁ := b21e14 X0 (σ x) (σ x)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e14
              | exact resolve b21e14 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e76 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
            have b21e80 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e76
                 have r₂ := b21e24
                 grind)
              | exact resolve b21e76 b21e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e76
            have b21e81 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b21e80
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e80
              | exact resolve b21e80 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e80
            have b21e120 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
              intro X0 X1
              first
              | (have i₁ := b21e40 X0
                 have i₂ := b21e40 X1
                 grind)
              | exact superpose b21e40 b21e40
              | exact resolve b21e40 b21e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e174 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b21e21
                 have i₂ := b21e120 (σ x) X0
                 grind)
              | (have i₁ := b21e21
                 have i₂ := b21e120 X0 (σ x)
                 grind)
              | exact superpose b21e120 b21e21
              | exact resolve b21e21 b21e120
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e120
            have b21e195 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (k x y)) := by
              intro X0
              first
              | (have i₁ := b21e40 X0
                 have i₂ := b21e81
                 grind)
              | exact superpose b21e81 b21e40
              | exact resolve b21e40 b21e81
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e40 b21e81
            have b21e340 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
              intro X0
              first
              | (have i₁ := b21e195 X0
                 have i₂ := b21e19 x y
                 grind)
              | exact superpose b21e19 b21e195
              | (have j1 := b21e19 x y
                 grind)
              | exact resolve b21e195 b21e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e195
            have b21e365 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
              intro X0
              first
              | (have j0 := b21e340 X0
                 grind)
              | (have r₁ := b21e340 X0
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e340 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e340
            have b21e367 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have j0 := b21e365 X0
                 grind)
              | (have r₁ := b21e365 X0
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e365 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e365
            have b21e368 : False := by grind
            exact b21e368
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b22e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
                intro X0 X1 X2
                grind
              have b22e19 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b22e23 : y ≠ (M.op x y) := by grind
              have b22e24 : y ≠ (M.op x x) := by grind
              have b22e25 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
              have b22e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e46 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (σ x)) := by
                intro X0
                first
                | (have i₁ := b22e15 X0 (σ x) (σ x)
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e15
                | exact resolve b22e15 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e79 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
              have b22e84 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b22e79
                   have r₂ := b22e25
                   grind)
                | exact resolve b22e79 b22e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e79
              have b22e85 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b22e84
                   have i₂ := b22e21 x y
                   grind)
                | exact superpose b22e21 b22e84
                | exact resolve b22e84 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e84
              have b22e187 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
                intro X0 X1
                first
                | (have i₁ := b22e46 X0
                   have i₂ := b22e46 X1
                   grind)
                | exact superpose b22e46 b22e46
                | exact resolve b22e46 b22e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e225 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (k x y)) := by
                intro X0
                first
                | (have i₁ := b22e46 X0
                   have i₂ := b22e85
                   grind)
                | exact superpose b22e85 b22e46
                | exact resolve b22e46 b22e85
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e46 b22e85
              have b22e1060 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b22e22
                   have i₂ := b22e187 (σ x) X0
                   grind)
                | (have i₁ := b22e22
                   have i₂ := b22e187 X0 (σ x)
                   grind)
                | exact superpose b22e187 b22e22
                | exact resolve b22e22 b22e187
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e187
              have b22e1931 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
                intro X0
                first
                | (have i₁ := b22e225 X0
                   have i₂ := b22e20 x y
                   grind)
                | exact superpose b22e20 b22e225
                | (have j1 := b22e20 x y
                   grind)
                | exact resolve b22e225 b22e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e225
              have b22e1982 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
                intro X0
                first
                | (have j0 := b22e1931 X0
                   grind)
                | (have r₁ := b22e1931 X0
                   have r₂ := b22e24
                   grind)
                | exact resolve b22e1931 b22e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e1931
              have b22e1987 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have j0 := b22e1982 X0
                   grind)
                | (have r₁ := b22e1982 X0
                   have r₂ := b22e23
                   grind)
                | exact resolve b22e1982 b22e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e1982
              have b22e1989 : False := by grind
              exact b22e1989
            · have b23e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
                intro X0 X1 X2
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b23e23 : y ≠ (M.op x y) := by grind
              have b23e24 : y ≠ (M.op x x) := by grind
              have b23e25 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
              have b23e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e38 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (σ x)) := by
                intro X0
                first
                | (have i₁ := b23e15 X0 (σ x) (σ x)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e15
                | exact resolve b23e15 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e69 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
              have b23e74 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e69
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e69 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e69
              have b23e75 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b23e74
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e74
                | exact resolve b23e74 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e74
              have b23e78 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
                intro X0 X1
                first
                | (have i₁ := b23e38 X0
                   have i₂ := b23e38 X1
                   grind)
                | exact superpose b23e38 b23e38
                | exact resolve b23e38 b23e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e107 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (k x y)) := by
                intro X0
                first
                | (have i₁ := b23e38 X0
                   have i₂ := b23e75
                   grind)
                | exact superpose b23e75 b23e38
                | exact resolve b23e38 b23e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e38 b23e75
              have b23e138 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b23e22
                   have i₂ := b23e78 (σ x) X0
                   grind)
                | (have i₁ := b23e22
                   have i₂ := b23e78 X0 (σ x)
                   grind)
                | exact superpose b23e78 b23e22
                | exact resolve b23e22 b23e78
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e78
              have b23e327 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
                intro X0
                first
                | (have i₁ := b23e107 X0
                   have i₂ := b23e20 x y
                   grind)
                | exact superpose b23e20 b23e107
                | (have j1 := b23e20 x y
                   grind)
                | exact resolve b23e107 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e107
              have b23e353 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
                intro X0
                first
                | (have j0 := b23e327 X0
                   grind)
                | (have r₁ := b23e327 X0
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e327 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e327
              have b23e355 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have j0 := b23e353 X0
                   grind)
                | (have r₁ := b23e353 X0
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e353 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e353
              have b23e356 : False := by grind
              exact b23e356
        · rcases eq_or_ne (M.op y x) (x) with h2a | h2a
          · have b24e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e22 : y ≠ (M.op x y) := by grind
            have b24e23 : y ≠ (M.op x x) := by grind
            have b24e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b24e25
                 have i₂ := b24e19 (σ x) X0
                 grind)
              | (have i₁ := b24e25
                 have i₂ := b24e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b24e19 b24e25
              | (have j1 := b24e19 (σ x) X0
                 grind)
              | (have r₁ := b24e25
                 have r₂ := b24e19 (σ x) (σ y)
                 grind)
              | exact resolve b24e25 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e1013 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have j0 := b24e65 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e65
            have b24e1014 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b24e1013
                 have r₂ := b24e24
                 grind)
              | exact resolve b24e1013 b24e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1013
            have b24e1015 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b24e1014
                 have i₂ := b24e20 x y
                 grind)
              | exact superpose b24e20 b24e1014
              | exact resolve b24e1014 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1014
            have b24e1018 : (σ (M.op x y)) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e1015
                 grind)
              | exact superpose b24e1015 b24e21
              | exact resolve b24e21 b24e1015
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1015
            have b24e1308 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b24e1018
                 have i₂ := b24e19 x y
                 grind)
              | exact superpose b24e19 b24e1018
              | (have j1 := b24e19 x y
                 grind)
              | exact resolve b24e1018 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1018
            have b24e1309 : y = (M.op x x) ∨ y = (M.op x y) := by grind
            clear b24e1308
            have b24e1311 : y = (M.op x y) := by
              first
              | (have r₁ := b24e1309
                 have r₂ := b24e23
                 grind)
              | exact resolve b24e1309 b24e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1309
            have b24e1313 : False := by grind
            exact b24e1313
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b25e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e23 : y ≠ (M.op x y) := by grind
              have b25e24 : y ≠ (M.op x x) := by grind
              have b25e25 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
              have b25e2376 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e62 x y
                   grind)
                | exact superpose b25e62 b25e22
                | (have j1 := b25e62 x y
                   grind)
                | exact resolve b25e22 b25e62
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e62
              have b25e2461 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b25e2376
                   have r₂ := b25e26
                   grind)
                | exact resolve b25e2376 b25e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2376
              have b25e2469 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have r₁ := b25e2461
                   have r₂ := b25e25
                   grind)
                | exact resolve b25e2461 b25e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2461
              have b25e2473 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b25e2469
                   have i₂ := b25e20 x y
                   grind)
                | exact superpose b25e20 b25e2469
                | (have j1 := b25e20 x y
                   grind)
                | exact resolve b25e2469 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2469
              have b25e2474 : y = (M.op x x) ∨ y = (M.op x y) := by grind
              clear b25e2473
              have b25e2476 : y = (M.op x y) := by
                first
                | (have r₁ := b25e2474
                   have r₂ := b25e24
                   grind)
                | exact resolve b25e2474 b25e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2474
              have b25e2478 : False := by grind
              exact b25e2478
            · have b26e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e23 : y ≠ (M.op x y) := by grind
              have b26e24 : y ≠ (M.op x x) := by grind
              have b26e25 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e54 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
                intro X0
                first
                | (have i₁ := b26e26
                   have i₂ := b26e20 (σ x) X0
                   grind)
                | (have i₁ := b26e26
                   have i₂ := b26e20 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b26e20 b26e26
                | (have j1 := b26e20 (σ x) X0
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e20 (σ x) (σ y)
                   grind)
                | exact resolve b26e26 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1039 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have j0 := b26e54 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e54
              have b26e1040 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b26e1039
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e1039 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1039
              have b26e1041 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b26e1040
                   have i₂ := b26e21 x y
                   grind)
                | exact superpose b26e21 b26e1040
                | exact resolve b26e1040 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1040
              have b26e1044 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e1041
                   grind)
                | exact superpose b26e1041 b26e22
                | exact resolve b26e22 b26e1041
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1041
              have b26e1312 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b26e1044
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e1044
                | (have j1 := b26e20 x y
                   grind)
                | exact resolve b26e1044 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1044
              have b26e1313 : y = (M.op x x) ∨ y = (M.op x y) := by grind
              clear b26e1312
              have b26e1315 : y = (M.op x y) := by
                first
                | (have r₁ := b26e1313
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e1313 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1313
              have b26e1317 : False := by grind
              exact b26e1317

/-- `Equation4514`: `x ◇ (y ◇ z) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_pxx_pxx_pxy_Equation4514 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4514 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4514.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X0) := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
      have b0e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 X0 (M.op X3 X1)
           have i₂ := b0e11 X0 X3 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) X3) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X3 (M.op X0 X2) X0
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ y) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ x) X0 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op y x) := by
        intro X0
        first
        | (have i₁ := b0e11 x X0 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e11 X0 X3 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e38 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e38
        | exact resolve b0e38 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e68 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 X1
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X0 X2)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X1 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e80 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e145 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (σ y))) = (M.op X1 (M.op X2 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e39 X1 X2 X0 (M.op X0 (σ x))
           have i₂ := b0e34 X0
           grind)
        | exact superpose b0e34 b0e39
        | exact resolve b0e39 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e147 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e39 X0 X1 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e39
        | exact resolve b0e39 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e187 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e147 X0 y
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e147
        | exact resolve b0e147 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e197 : ∀ X0 : G, (M.op (M.op X0 x) X0) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 x x
           have i₂ := b0e147 X0 x
           grind)
        | exact superpose b0e147 b0e11
        | exact resolve b0e11 b0e147
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e147
      have b0e306 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e39 X0 x y X1
           have i₂ := b0e187 X0
           grind)
        | exact superpose b0e187 b0e39
        | exact resolve b0e39 b0e187
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e187
      have b0e379 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e39 X1 X2 X0 (M.op X0 x)
           have i₂ := b0e197 X0
           grind)
        | exact superpose b0e197 b0e39
        | exact resolve b0e39 b0e197
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e197
      have b0e394 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e379 X0 X1 X2
           have i₂ := b0e306 X1 X0
           grind)
        | exact superpose b0e306 b0e379
        | exact resolve b0e379 b0e306
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e306 b0e379
      have b0e495 : ∀ X0 X1 : G, (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (M.op X0 X1) X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e37 (M.op (σ x) (M.op x X1))
           have i₂ := b0e32 X0 X1 (σ x) x
           grind)
        | exact superpose b0e32 b0e37
        | exact resolve b0e37 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e37
      have b0e525 : (M.op (σ y) (σ x)) = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e495 x x
           have i₂ := b0e394 (M.op (M.op x x) x) (σ x) (σ x)
           grind)
        | exact superpose b0e394 b0e495
        | exact resolve b0e495 b0e394
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e495
      have b0e1942 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e394 (σ x) X0 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e394
        | exact resolve b0e394 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1973 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e33 X1 x x X0
           have i₂ := b0e394 (M.op x x) X0 X1
           grind)
        | exact superpose b0e394 b0e33
        | exact resolve b0e33 b0e394
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e2114 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e1942 (σ x)
           grind)
        | exact superpose b0e1942 b0e18
        | exact resolve b0e18 b0e1942
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1942
      have b0e2320 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e68 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e2322 : ∀ X0 X1 : G, (M.op X1 y) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e2320 X0 X1 x
           have i₂ := b0e394 X1 X1 x
           grind)
        | exact superpose b0e394 b0e2320
        | (have j0 := b0e2320 X0 X1 x
           grind)
        | (have r₁ := b0e2320 (M.op X0 y) X0 x
           have r₂ := b0e394 X0 X0 x
           grind)
        | exact resolve b0e2320 b0e394
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2320
      have b0e6511 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (σ y))) = X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X2 (M.op X0 X1)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e16 (M.op X0 X1) X2
           have i₂ := b0e145 X1 (M.op X0 X1) X0
           grind)
        | (have i₁ := b0e16 (M.op X0 (σ y)) X1
           have i₂ := b0e145 X0 (M.op X0 (σ y)) X2
           grind)
        | exact superpose b0e145 b0e16
        | (have j0 := b0e16 (M.op X0 X1) X2
           grind)
        | exact resolve b0e16 b0e145
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e145
      have b0e6592 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X2 (M.op X0 X1)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e6511 X0 X1 X2
           have i₂ := b0e394 (σ y) (M.op X0 X1) X1
           grind)
        | exact superpose b0e394 b0e6511
        | (have j0 := b0e6511 X0 X1 X2
           grind)
        | exact resolve b0e6511 b0e394
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6511
      have b0e6741 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X2 (M.op X0 X1)) = X2 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e6592 X0 X1 X2
           have j1 := b0e2322 X2 (M.op X0 X1)
           grind)
        | (have r₁ := b0e6592 X0 X1 X0
           have r₂ := b0e2322 X0 (M.op X0 X1)
           grind)
        | (have r₁ := b0e6592 X0 X1 (M.op X1 y)
           have r₂ := b0e2322 (M.op (M.op X0 X1) y) X1
           grind)
        | (have r₁ := b0e6592 X0 X1 y
           have r₂ := b0e2322 (k (M.op X0 X1) y) (M.op X0 X1)
           grind)
        | exact resolve b0e6592 b0e2322
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2322 b0e6592
      have b0e6830 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X2 y) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e6741 X0 X1 X2
           have i₂ := b0e394 X1 X2 X0
           grind)
        | exact superpose b0e394 b0e6741
        | (have j0 := b0e6741 X0 X1 X2
           grind)
        | exact resolve b0e6741 b0e394
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e394 b0e6741
      have b0e84381 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e6830 (σ x) (σ x) x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e6830
        | (have j0 := b0e6830 X0 x X0
           grind)
        | exact resolve b0e6830 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e84394 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e6830 x x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e6830
        | (have j0 := b0e6830 X0 x X0
           grind)
        | exact resolve b0e6830 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6830
      have b0e85236 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) ∨ (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e80 y X0
           have i₂ := b0e84381 X0
           grind)
        | exact superpose b0e84381 b0e80
        | (have j1 := b0e84381 X0
           grind)
        | exact resolve b0e80 b0e84381
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e80 b0e84381
      have b0e86405 : (k y (τ (σ x))) = (τ (M.op (σ x) y)) ∨ (σ x) = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e85236 (σ x)
           have i₂ := b0e525
           grind)
        | exact superpose b0e525 b0e85236
        | (have j0 := b0e85236 (σ x)
           grind)
        | exact resolve b0e85236 b0e525
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e525 b0e85236
      have b0e86521 : (k y x) = (τ (M.op (σ x) y)) ∨ (σ x) = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e86405
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e86405
        | exact resolve b0e86405 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e86405
      have b0e103073 : (M.op (σ x) y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e13 (M.op (σ x) y)
           have i₂ := b0e86521
           grind)
        | exact superpose b0e86521 b0e13
        | exact resolve b0e13 b0e86521
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e86521
      have b0e115310 : (M.op (σ x) y) = (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e103073
           have i₂ := b0e84394 x
           grind)
        | exact superpose b0e84394 b0e103073
        | (have j1 := b0e84394 (σ x)
           grind)
        | exact resolve b0e103073 b0e84394
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e84394 b0e103073
      have b0e115425 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e115310
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e115310
        | exact resolve b0e115310 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e115310
      have b0e115468 : (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
        first
        | (have r₁ := b0e115425
           have r₂ := b0e2114
           grind)
        | exact resolve b0e115425 b0e2114
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2114 b0e115425
      have b0e115729 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e1973 (σ x) y
           have i₂ := b0e115468
           grind)
        | exact superpose b0e115468 b0e1973
        | exact resolve b0e1973 b0e115468
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e115468
      have b0e115758 : x = (M.op x y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e115729
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e115729
        | exact resolve b0e115729 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e115729
      have b0e117274 : x = (M.op x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e1973 x y
           have i₂ := b0e115758
           grind)
        | exact superpose b0e115758 b0e1973
        | exact resolve b0e1973 b0e115758
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1973 b0e115758
      have b0e117298 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e117274
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e117274
        | exact resolve b0e117274 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117274
      have b0e118762 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e117298
           grind)
        | exact superpose b0e117298 b0e12
        | exact resolve b0e12 b0e117298
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117298
      have b0e118857 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e118762
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e118762
        | exact resolve b0e118762 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e118762
      have b0e118858 : x = y := by grind
      clear b0e118857
      have b0e119731 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e118858
           grind)
        | exact superpose b0e118858 b0e18
        | exact resolve b0e18 b0e118858
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e118858
      have b0e119888 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e119731
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e119731
        | exact resolve b0e119731 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e119731
      have b0e119918 : False := by grind
      exact b0e119918
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : y = (k x y) := by grind
        have b1e47 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b1e50 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e47
        have b1e52 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e50
             have r₂ := b1e21
             grind)
          | exact resolve b1e50 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e53 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e52
          | exact resolve b1e52 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e54 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e24
             grind)
          | exact superpose b1e24 b1e53
          | exact resolve b1e53 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e53
        have b1e55 : False := by grind
        exact b1e55
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X0) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : y = (k x y) := by grind
        have b2e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X2 X0 (M.op X3 X1)
             have i₂ := b2e12 X0 X3 X1
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) X3) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X3 (M.op X0 X2) X0
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b2e12 x X0 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e12 X0 X3 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b2e29 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e29
          | exact resolve b2e29 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e60 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 (σ x) X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e100 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b2e32 X0 X1 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e32
          | exact resolve b2e32 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e134 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e100 X0 y
             have i₂ := b2e33
             grind)
          | exact superpose b2e33 b2e100
          | exact resolve b2e100 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e189 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op (M.op X1 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e28 X0 x x X1
             have i₂ := b2e100 X0 x
             grind)
          | exact superpose b2e100 b2e28
          | exact resolve b2e28 b2e100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e100
        have b2e227 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 y)) := by
          intro X0 X1
          first
          | (have i₁ := b2e32 X0 x y X1
             have i₂ := b2e134 X0
             grind)
          | exact superpose b2e134 b2e32
          | exact resolve b2e32 b2e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e134
        have b2e322 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op X0 (M.op X4 X3)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e32 X0 (M.op X3 X2) X3 X4
             have i₂ := b2e27 X3 X2 X0 X1
             grind)
          | exact superpose b2e27 b2e32
          | exact resolve b2e32 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e32
        have b2e338 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op X0 (M.op (M.op X1 X2) y)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e322 X0 X1 X2 X3 X4
             have i₂ := b2e189 (M.op X1 X2) X0
             grind)
          | exact superpose b2e189 b2e322
          | exact resolve b2e322 b2e189
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e189 b2e322
        have b2e396 : ∀ X0 X3 X4 : G, (M.op X0 y) = (M.op X0 (M.op X4 X3)) := by
          intro X0 X3 X4
          first
          | (have i₁ := b2e338 X0 x x X3 X4
             have i₂ := b2e227 X0 (M.op x x)
             grind)
          | exact superpose b2e227 b2e338
          | exact resolve b2e338 b2e227
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e227 b2e338
        have b2e533 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b2e28 X1 x x X0
             have i₂ := b2e396 X0 (M.op x x) X1
             grind)
          | exact superpose b2e396 b2e28
          | exact resolve b2e28 b2e396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e1571 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e60 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e1572 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1571
             have r₂ := b2e22
             grind)
          | exact resolve b2e1571 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1571
        have b2e1573 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1572
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1572
          | exact resolve b2e1572 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1572
        have b2e1574 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1573
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1573
          | exact resolve b2e1573 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1573
        have b2e1588 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e396 X0 (σ y) (σ x)
             have i₂ := b2e1574
             grind)
          | exact superpose b2e1574 b2e396
          | exact resolve b2e396 b2e1574
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e396
        have b2e2314 : (σ y) = (M.op (σ x) y) := by
          first
          | (have i₁ := b2e1574
             have i₂ := b2e1588 (σ x)
             grind)
          | exact superpose b2e1588 b2e1574
          | exact resolve b2e1574 b2e1588
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1574 b2e1588
        have b2e2539 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e533 (σ x) y
             have i₂ := b2e2314
             grind)
          | exact superpose b2e2314 b2e533
          | exact resolve b2e533 b2e2314
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e533 b2e2314
        have b2e2540 : False := by grind
        exact b2e2540
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
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
        have b3e56 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b3e58 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
        clear b3e56
        have b3e59 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e58
             have r₂ := b3e20
             grind)
          | exact resolve b3e58 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e60 : y = (M.op x x) := by
          first
          | (have i₁ := b3e59
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e59
          | exact resolve b3e59 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e59
        have b3e61 : False := by grind
        exact b3e61
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X0) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op x x) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
          have b4e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 X0 (M.op X3 X1)
               have i₂ := b4e13 X0 X3 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) X3) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X3 (M.op X0 X2) X0
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e30 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X0 X1 X2
               have i₂ := b4e13 X0 X3 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b4e17 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 (σ x) (σ y)
               grind)
            | (have r₁ := b4e17 (σ x) (σ y)
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have i₁ := b4e17 x y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 x y
               grind)
            | (have r₁ := b4e17 x y
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e47 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
          clear b4e45
          have b4e48 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b4e44
          have b4e49 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b4e47
               have r₂ := b4e21
               grind)
            | exact resolve b4e47 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47
          have b4e50 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e48
               have r₂ := b4e23
               grind)
            | exact resolve b4e48 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e51 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e50
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e50
            | exact resolve b4e50 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e51
               have i₂ := b4e49
               grind)
            | exact superpose b4e49 b4e51
            | exact resolve b4e51 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49 b4e51
          have b4e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b4e60 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X2 X1
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e13 X0 X1 X2
               have i₂ := b4e18 X0 (M.op X0 X2)
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e68 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          clear b4e26
          have b4e75 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          clear b4e27
          have b4e84 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = (M.op X0 (σ (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ x) (σ x)
               have i₂ := b4e52
               grind)
            | exact superpose b4e52 b4e13
            | exact resolve b4e13 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e85 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b4e84 X0
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e84
            | exact resolve b4e84 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84
          have b4e92 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (σ x))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 (σ x)
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e13
            | exact resolve b4e13 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e95 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op X1 (M.op X0 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op X0 (σ x)) X0
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e13
            | exact resolve b4e13 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e121 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (σ y))) = (M.op X1 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e35 X1 X2 X0 (M.op X0 (σ x))
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e35
            | exact resolve b4e35 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30
          have b4e124 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e35 X0 X1 x y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e35
            | exact resolve b4e35 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e144 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (k (M.op X0 X1) X3) ∨ (M.op (M.op X0 X1) (M.op X2 X1)) = X3 ∨ (M.op X3 (M.op X0 X1)) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e18 (M.op X0 X1) X3
               have i₂ := b4e35 (M.op X0 X1) X0 X1 X2
               grind)
            | (have i₁ := b4e18 (M.op X0 X1) X3
               have i₂ := b4e35 (M.op X0 X1) X2 X1 X0
               grind)
            | exact superpose b4e35 b4e18
            | (have j0 := b4e18 (M.op X0 X1) X3
               grind)
            | exact resolve b4e18 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e155 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op X2 (M.op x (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e124 X2 (M.op x X1)
               have i₂ := b4e13 x X0 X1
               grind)
            | exact superpose b4e13 b4e124
            | exact resolve b4e124 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e165 : ∀ X0 : G, (M.op (M.op X0 x) X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 x x
               have i₂ := b4e124 X0 x
               grind)
            | exact superpose b4e124 b4e13
            | exact resolve b4e13 b4e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e214 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op X1 (M.op X0 y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e29 X0 x x X1
               have i₂ := b4e124 X0 x
               grind)
            | exact superpose b4e124 b4e29
            | exact resolve b4e29 b4e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29
          have b4e279 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e35 X1 X2 X0 (M.op X0 x)
               have i₂ := b4e165 X0
               grind)
            | exact superpose b4e165 b4e35
            | exact resolve b4e35 b4e165
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e285 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b4e124 X0 (M.op x x)
               have i₂ := b4e165 x
               grind)
            | exact superpose b4e165 b4e124
            | exact resolve b4e124 b4e165
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e124
          have b4e331 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e35 X0 x y X1
               have i₂ := b4e285 X0
               grind)
            | exact superpose b4e285 b4e35
            | exact resolve b4e35 b4e285
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e382 : ∀ X0 X1 : G, (M.op (M.op X0 y) X0) = (M.op X0 (M.op (M.op X1 y) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e28 X1 y X0 x
               have i₂ := b4e285 X0
               grind)
            | exact superpose b4e285 b4e28
            | exact resolve b4e28 b4e285
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e285
          have b4e516 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op (M.op X0 y) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e382 X0 X1
               have i₂ := b4e121 X1 X0 (M.op X1 y)
               grind)
            | (have i₁ := b4e382 X1 (σ y)
               have i₂ := b4e121 (M.op (σ y) y) X1 x
               grind)
            | exact superpose b4e121 b4e382
            | exact resolve b4e382 b4e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e382
          have b4e574 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op X0 (M.op y y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e516 X0 X1
               have i₂ := b4e214 y X0
               grind)
            | exact superpose b4e214 b4e516
            | exact resolve b4e516 b4e214
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e516
          have b4e612 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e574 X0 X1
               have i₂ := b4e331 X0 y
               grind)
            | exact superpose b4e331 b4e574
            | exact resolve b4e574 b4e331
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e331 b4e574
          have b4e1842 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e60 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e2974 : (σ x) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (k x x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e56 x x
               have i₂ := b4e52
               grind)
            | exact superpose b4e52 b4e56
            | exact resolve b4e56 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56
          have b4e3071 : (σ (M.op x x)) = (σ (k x x)) ∨ (σ x) = (σ (M.op x x)) := by grind
          clear b4e2974
          have b4e3882 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) y)) := by
            intro X0
            first
            | (have i₁ := b4e92 X0 (M.op (σ x) x)
               have i₂ := b4e165 (σ x)
               grind)
            | exact superpose b4e165 b4e92
            | exact resolve b4e92 b4e165
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92 b4e165
          have b4e3984 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op y (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e3882 X0
               have i₂ := b4e121 y X0 (σ x)
               grind)
            | exact superpose b4e121 b4e3882
            | exact resolve b4e3882 b4e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3882
          have b4e4011 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e3984 X0
               have i₂ := b4e612 X0 y
               grind)
            | exact superpose b4e612 b4e3984
            | exact resolve b4e3984 b4e612
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3984
          have b4e4080 : (M.op (σ (M.op x x)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b4e95 (σ x) (σ x)
               have i₂ := b4e52
               grind)
            | exact superpose b4e52 b4e95
            | exact resolve b4e95 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e4171 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e612 X0 X1
               have i₂ := b4e95 X1 X0
               grind)
            | exact superpose b4e95 b4e612
            | exact resolve b4e612 b4e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e95
          have b4e4289 : (M.op (σ (M.op x x)) (σ x)) = (M.op (σ x) (M.op (σ y) y)) := by
            first
            | (have i₁ := b4e4080
               have i₂ := b4e279 (σ y) (σ x) (σ x)
               grind)
            | exact superpose b4e279 b4e4080
            | exact resolve b4e4080 b4e279
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e279 b4e4080
          have b4e4370 : (M.op (σ (M.op x x)) (σ x)) = (M.op (σ x) (M.op y (σ y))) := by
            first
            | (have i₁ := b4e4289
               have i₂ := b4e121 y (σ x) (σ y)
               grind)
            | exact superpose b4e121 b4e4289
            | exact resolve b4e4289 b4e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4289
          have b4e4426 : (M.op (σ (M.op x x)) (σ x)) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e4370
               have i₂ := b4e612 (σ x) y
               grind)
            | exact superpose b4e612 b4e4370
            | exact resolve b4e4370 b4e612
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4370
          have b4e4520 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e4011 (σ x)
               grind)
            | exact superpose b4e4011 b4e20
            | exact resolve b4e20 b4e4011
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e4730 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e612 X0 X2
               have i₂ := b4e121 X2 X0 X1
               grind)
            | (have i₁ := b4e612 X1 X2
               have i₂ := b4e121 (σ y) X1 X2
               grind)
            | exact superpose b4e121 b4e612
            | exact resolve b4e612 b4e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e4804 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (σ y))) = X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X2 (M.op X0 X1)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e18 (M.op X0 X1) X2
               have i₂ := b4e121 X1 (M.op X0 X1) X0
               grind)
            | (have i₁ := b4e18 (M.op X0 (σ y)) X1
               have i₂ := b4e121 X0 (M.op X0 (σ y)) X2
               grind)
            | exact superpose b4e121 b4e18
            | (have j0 := b4e18 (M.op X0 X1) X2
               grind)
            | exact resolve b4e18 b4e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e121
          have b4e4868 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X2 (M.op X0 X1)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e4804 X0 X1 X2
               have i₂ := b4e612 (M.op X0 X1) X1
               grind)
            | exact superpose b4e612 b4e4804
            | (have j0 := b4e4804 X0 X1 X2
               grind)
            | exact resolve b4e4804 b4e612
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e612 b4e4804
          have b4e5008 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) y) = X2 ∨ (M.op X2 y) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e4868 X0 X1 X2
               have i₂ := b4e4730 X2 X0 X1
               grind)
            | exact superpose b4e4730 b4e4868
            | (have j0 := b4e4868 X0 X1 X2
               grind)
            | exact resolve b4e4868 b4e4730
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4868
          have b4e25902 : (k x x) = (τ (σ (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e14 (k x x)
               have i₂ := b4e3071
               grind)
            | exact superpose b4e3071 b4e14
            | exact resolve b4e14 b4e3071
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3071
          have b4e25938 : (σ x) = (σ (M.op x x)) ∨ (M.op x x) = (k x x) := by
            first
            | (have i₁ := b4e25902
               have i₂ := b4e14 (M.op x x)
               grind)
            | exact superpose b4e14 b4e25902
            | exact resolve b4e25902 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25902
          have b4e39576 : ∀ X0 : G, (k (τ X0) (M.op x x)) = (τ (k X0 (σ x))) ∨ (M.op x x) = (k x x) := by
            intro X0
            first
            | (have i₁ := b4e68 X0 (M.op x x)
               have i₂ := b4e25938
               grind)
            | exact superpose b4e25938 b4e68
            | exact resolve b4e68 b4e25938
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25938
          have b4e39587 : ∀ X0 : G, (k (τ X0) (M.op x x)) = (k (τ X0) x) ∨ (M.op x x) = (k x x) := by
            intro X0
            first
            | (have i₁ := b4e39576 X0
               have i₂ := b4e68 X0 x
               grind)
            | exact superpose b4e68 b4e39576
            | exact resolve b4e39576 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68 b4e39576
          have b4e80809 : ∀ X0 X2 : G, (M.op X0 y) ≠ X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X2 X0) = X2 := by
            intro X0 X2
            first
            | (have i₁ := b4e1842 X2 X0 x
               have i₂ := b4e4730 X0 x X0
               grind)
            | exact superpose b4e4730 b4e1842
            | (have j0 := b4e1842 X2 X0 X2
               grind)
            | (have r₁ := b4e1842 (M.op X2 y) X2 x
               have r₂ := b4e4730 X2 x X2
               grind)
            | exact resolve b4e1842 b4e4730
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e80832 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) ≠ X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X2 (M.op X0 X1)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e1842 X2 (M.op X0 X1) x
               have i₂ := b4e155 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b4e155 b4e1842
            | (have j0 := b4e1842 X2 (M.op X0 X1) X2
               grind)
            | (have r₁ := b4e1842 (M.op (M.op X0 X1) y) (M.op X0 X1) x
               have r₂ := b4e155 X0 X1 (M.op X0 X1)
               grind)
            | exact resolve b4e1842 b4e155
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e155 b4e1842
          have b4e80863 : ∀ X0 X1 X2 : G, (M.op X2 y) = X2 ∨ (M.op (M.op X0 X1) y) ≠ X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e80832 X0 X1 X2
               have i₂ := b4e4730 X2 X0 X1
               grind)
            | exact superpose b4e4730 b4e80832
            | (have j0 := b4e80832 X0 X1 X2
               grind)
            | (have r₁ := b4e80832 X0 X1 (M.op (M.op X0 X1) (M.op X1 X2))
               have r₂ := b4e4730 (M.op X0 X1) X1 X2
               grind)
            | exact resolve b4e80832 b4e4730
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80832
          have b4e81008 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X2 y) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e80863 X0 X1 X2
               have j1 := b4e5008 X0 X1 X2
               grind)
            | (have r₁ := b4e80863 X0 X1 (k (M.op X0 X1) y)
               have r₂ := b4e5008 X0 X1 y
               grind)
            | (have r₁ := b4e80863 X0 X1 X2
               have r₂ := b4e5008 X0 X1 X2
               grind)
            | (have r₁ := b4e80863 X0 X1 (M.op (M.op X0 X1) y)
               have r₂ := b4e5008 X0 X1 (M.op (M.op X0 X1) y)
               grind)
            | exact resolve b4e80863 b4e5008
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5008 b4e80863
          have b4e211247 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) (M.op X0 (σ x))) = X1 ∨ (M.op (σ (M.op x x)) X1) = (k (σ (M.op x x)) X1) ∨ (M.op X1 (σ (M.op x x))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e144 (σ x) (σ x) x x
               have i₂ := b4e52
               grind)
            | exact superpose b4e52 b4e144
            | exact resolve b4e144 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e144
          have b4e212606 : ∀ X1 : G, (M.op (σ (M.op x x)) y) = X1 ∨ (M.op (σ (M.op x x)) X1) = (k (σ (M.op x x)) X1) ∨ (M.op X1 (σ (M.op x x))) = X1 := by
            intro X1
            first
            | (have i₁ := b4e211247 x X1
               have i₂ := b4e4730 (σ (M.op x x)) x (σ x)
               grind)
            | exact superpose b4e4730 b4e211247
            | (have j0 := b4e211247 x X1
               grind)
            | exact resolve b4e211247 b4e4730
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e211247
          have b4e213512 : ∀ X1 : G, (M.op (σ (M.op x x)) X1) = (k (σ (M.op x x)) X1) ∨ (M.op X1 (σ (M.op x x))) = X1 := by
            intro X1
            first
            | (have j0 := b4e212606 X1
               have j1 := b4e80809 (σ (M.op x x)) X1
               grind)
            | (have r₁ := b4e212606 x
               have r₂ := b4e80809 (σ (M.op x x)) x
               grind)
            | (have r₁ := b4e212606 (M.op x y)
               have r₂ := b4e80809 x (M.op (σ (M.op x x)) y)
               grind)
            | (have r₁ := b4e212606 y
               have r₂ := b4e80809 (σ (M.op x x)) (k (σ (M.op x x)) y)
               grind)
            | exact resolve b4e212606 b4e80809
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80809 b4e212606
          have b4e214297 : ∀ X1 : G, (M.op X1 (σ y)) = X1 ∨ (M.op (σ (M.op x x)) X1) = (k (σ (M.op x x)) X1) := by
            intro X1
            first
            | (have i₁ := b4e213512 X1
               have i₂ := b4e85 X1
               grind)
            | exact superpose b4e85 b4e213512
            | (have j0 := b4e213512 X1
               grind)
            | exact resolve b4e213512 b4e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85 b4e213512
          have b4e214925 : ∀ X1 : G, (M.op (σ (M.op x x)) X1) = (k (σ (M.op x x)) X1) ∨ (M.op X1 y) = X1 := by
            intro X1
            first
            | (have i₁ := b4e214297 X1
               have i₂ := b4e4011 X1
               grind)
            | exact superpose b4e4011 b4e214297
            | (have j0 := b4e214297 X1
               grind)
            | exact resolve b4e214297 b4e4011
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4011 b4e214297
          have b4e534485 : ∀ X0 : G, (k (M.op x x) (τ X0)) = (τ (M.op (σ (M.op x x)) X0)) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e75 (M.op x x) X0
               have i₂ := b4e214925 X0
               grind)
            | exact superpose b4e214925 b4e75
            | (have j1 := b4e214925 X0
               grind)
            | exact resolve b4e75 b4e214925
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75 b4e214925
          have b4e585348 : ∀ X0 : G, (k X0 x) = (k X0 (M.op x x)) ∨ (M.op x x) = (k x x) := by
            intro X0
            first
            | (have i₁ := b4e39587 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e39587
            | exact resolve b4e39587 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39587
          have b4e585559 : (M.op x x) = (k x x) ∨ (M.op x x) = (k x x) := by grind
          clear b4e585348
          have b4e585604 : (M.op x x) = (k x x) := by grind
          clear b4e585559
          have b4e1501437 : (τ (M.op (σ x) y)) = (k (M.op x x) (τ (σ x))) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e534485 (σ x)
               have i₂ := b4e4426
               grind)
            | exact superpose b4e4426 b4e534485
            | (have j0 := b4e534485 (σ x)
               grind)
            | exact resolve b4e534485 b4e4426
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4426 b4e534485
          have b4e1501452 : (k (M.op x x) x) = (τ (M.op (σ x) y)) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e1501437
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e1501437
            | exact resolve b4e1501437 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1501437
          have b4e1501468 : (M.op (σ x) y) = (σ (k (M.op x x) x)) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e15 (M.op (σ x) y)
               have i₂ := b4e1501452
               grind)
            | exact superpose b4e1501452 b4e15
            | exact resolve b4e15 b4e1501452
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1501452
          have b4e1501479 : (M.op (σ x) y) = (σ (M.op (M.op x x) x)) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e1501468
               have i₂ := b4e81008 x x x
               grind)
            | exact superpose b4e81008 b4e1501468
            | (have j1 := b4e81008 x x (σ x)
               grind)
            | exact resolve b4e1501468 b4e81008
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81008
          have b4e1501501 : (M.op (σ x) y) = (σ (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e1501479
               have i₂ := b4e214 x x
               grind)
            | exact superpose b4e214 b4e1501479
            | exact resolve b4e1501479 b4e214
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e214 b4e1501479
          have b4e1501502 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e1501501
               have i₂ := b4e4730 x x y
               grind)
            | exact superpose b4e4730 b4e1501501
            | exact resolve b4e1501501 b4e4730
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1501501
          have b4e1501503 : (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e1501502
               have r₂ := b4e4520
               grind)
            | exact resolve b4e1501502 b4e4520
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1501502
          have b4e1503988 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e4171 (σ x) y
               have i₂ := b4e1501503
               grind)
            | exact superpose b4e1501503 b4e4171
            | exact resolve b4e4171 b4e1501503
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1501503
          have b4e1504023 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e1503988
               have i₂ := b4e52
               grind)
            | exact superpose b4e52 b4e1503988
            | exact resolve b4e1503988 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52 b4e1503988
          have b4e1505503 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e14 (M.op x x)
               have i₂ := b4e1504023
               grind)
            | exact superpose b4e1504023 b4e14
            | exact resolve b4e14 b4e1504023
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1504023
          have b4e1505560 : x = (M.op x y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e1505503
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e1505503
            | exact resolve b4e1505503 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1505503
          have b4e1508664 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e4171 x y
               have i₂ := b4e1505560
               grind)
            | exact superpose b4e1505560 b4e4171
            | exact resolve b4e4171 b4e1505560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4171 b4e1505560
          have b4e1508701 : x = (M.op x x) := by grind
          clear b4e1508664
          have b4e1512839 : (M.op (σ x) y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e1501468
               have i₂ := b4e1508701
               grind)
            | exact superpose b4e1508701 b4e1501468
            | exact resolve b4e1501468 b4e1508701
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1501468
          have b4e1513045 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e4730 X0 x x
               have i₂ := b4e1508701
               grind)
            | exact superpose b4e1508701 b4e4730
            | exact resolve b4e4730 b4e1508701
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4730
          have b4e1513215 : (σ (M.op x x)) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e1512839
               have i₂ := b4e585604
               grind)
            | exact superpose b4e585604 b4e1512839
            | exact resolve b4e1512839 b4e585604
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e585604 b4e1512839
          have b4e1513298 : (σ (M.op x x)) = (M.op (σ x) x) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e1513215
               have i₂ := b4e1513045 (σ x)
               grind)
            | exact superpose b4e1513045 b4e1513215
            | exact resolve b4e1513215 b4e1513045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1513215
          have b4e1513345 : (σ x) = (M.op (σ x) x) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e1513298
               have i₂ := b4e1508701
               grind)
            | exact superpose b4e1508701 b4e1513298
            | exact resolve b4e1513298 b4e1508701
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1513298
          have b4e1513376 : (σ x) = (M.op (σ x) x) ∨ (σ x) = (M.op (σ x) x) := by
            first
            | (have i₁ := b4e1513345
               have i₂ := b4e1513045 (σ x)
               grind)
            | exact superpose b4e1513045 b4e1513345
            | exact resolve b4e1513345 b4e1513045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1513345
          have b4e1513377 : (σ x) = (M.op (σ x) x) := by grind
          clear b4e1513376
          have b4e1522258 : (σ (M.op x x)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e4520
               have i₂ := b4e1513045 x
               grind)
            | exact superpose b4e1513045 b4e4520
            | exact resolve b4e4520 b4e1513045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4520
          have b4e1523115 : (σ (M.op x x)) ≠ (M.op (σ x) x) := by
            first
            | (have i₁ := b4e1522258
               have i₂ := b4e1513045 (σ x)
               grind)
            | exact superpose b4e1513045 b4e1522258
            | exact resolve b4e1522258 b4e1513045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1513045 b4e1522258
          have b4e1523493 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e1523115
               have i₂ := b4e1513377
               grind)
            | exact superpose b4e1513377 b4e1523115
            | exact resolve b4e1523115 b4e1513377
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1513377 b4e1523115
          have b4e1523722 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e1523493
               have i₂ := b4e1508701
               grind)
            | exact superpose b4e1508701 b4e1523493
            | exact resolve b4e1523493 b4e1508701
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1508701 b4e1523493
          have b4e1523723 : False := by grind
          exact b4e1523723
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X0) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e19
            | exact resolve b5e19 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 X0 (M.op X3 X1)
               have i₂ := b5e13 X0 X3 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) X3) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X3 (M.op X0 X2) X0
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b5e13 y X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e13 X0 X3 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
          have b5e44 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
          clear b5e40
          have b5e45 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e44
               have r₂ := b5e21
               grind)
            | exact resolve b5e44 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e51 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e53 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 X1
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X0 X2)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X1 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e55 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ x) X0
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 (σ x) X0
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e93 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 X0 X1 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e33
            | exact resolve b5e33 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e130 : ∀ X0 : G, (M.op (M.op X0 x) X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x x
               have i₂ := b5e93 X0 x
               grind)
            | exact superpose b5e93 b5e13
            | exact resolve b5e13 b5e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e174 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op (M.op X1 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e29 X0 x x X1
               have i₂ := b5e93 X0 x
               grind)
            | exact superpose b5e93 b5e29
            | exact resolve b5e29 b5e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e217 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 y)) = (M.op X1 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33 X1 X2 X0 (M.op X0 x)
               have i₂ := b5e130 X0
               grind)
            | exact superpose b5e130 b5e33
            | exact resolve b5e33 b5e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e222 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b5e93 X0 (M.op x x)
               have i₂ := b5e130 x
               grind)
            | exact superpose b5e130 b5e93
            | exact resolve b5e93 b5e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e93
          have b5e223 : (M.op y y) = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b5e30 (M.op x x)
               have i₂ := b5e130 x
               grind)
            | exact superpose b5e130 b5e30
            | exact resolve b5e30 b5e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e130
          have b5e301 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op X0 (M.op X4 X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e33 X0 (M.op X3 X2) X3 X4
               have i₂ := b5e28 X3 X2 X0 X1
               grind)
            | exact superpose b5e28 b5e33
            | exact resolve b5e33 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e317 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op X0 (M.op (M.op X1 X2) y)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e301 X0 X1 X2 X3 X4
               have i₂ := b5e174 (M.op X1 X2) X0
               grind)
            | exact superpose b5e174 b5e301
            | exact resolve b5e301 b5e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e174 b5e301
          have b5e369 : ∀ X0 X3 X4 : G, (M.op X0 (M.op y y)) = (M.op X0 (M.op X4 X3)) := by
            intro X0 X3 X4
            first
            | (have i₁ := b5e317 X0 x x X3 X4
               have i₂ := b5e217 y X0 (M.op x x)
               grind)
            | (have i₁ := b5e317 x x x X3 X4
               have i₂ := b5e217 (M.op x x) x x
               grind)
            | exact superpose b5e217 b5e317
            | exact resolve b5e317 b5e217
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e217 b5e317
          have b5e426 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 X0 x y X1
               have i₂ := b5e222 X0
               grind)
            | exact superpose b5e222 b5e33
            | exact resolve b5e33 b5e222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33 b5e222
          have b5e1328 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e51 (σ X1) (σ X0)
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e51
            | (have j0 := b5e51 (σ X1) (σ X0)
               grind)
            | exact resolve b5e51 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e1353 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e55 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e1354 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1353
               have r₂ := b5e24
               grind)
            | exact resolve b5e1353 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1353
          have b5e1355 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1354
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1354
            | exact resolve b5e1354 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1354
          have b5e1356 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1355
               have i₂ := b5e45
               grind)
            | exact superpose b5e45 b5e1355
            | exact resolve b5e1355 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45 b5e1355
          have b5e1357 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e1356
               grind)
            | exact superpose b5e1356 b5e20
            | exact resolve b5e20 b5e1356
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1363 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 (M.op X1 (σ (M.op x x)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e29 X1 (σ x) (σ y) X0
               have i₂ := b5e1356
               grind)
            | exact superpose b5e1356 b5e29
            | exact resolve b5e29 b5e1356
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e1376 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 (M.op y y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e1363 X0 X1
               have i₂ := b5e369 X0 (σ (M.op x x)) X1
               grind)
            | exact superpose b5e369 b5e1363
            | exact resolve b5e1363 b5e369
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e369 b5e1363
          have b5e1388 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b5e1376 X0 X1
               have i₂ := b5e426 X0 y
               grind)
            | exact superpose b5e426 b5e1376
            | exact resolve b5e1376 b5e426
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e426 b5e1376
          have b5e1528 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e53 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e2086 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e1388 X0 X2
               grind)
            | exact superpose b5e1388 b5e13
            | exact resolve b5e13 b5e1388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e62382 : ∀ X0 : G, (M.op y y) ≠ X0 ∨ (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1528 X0 y x
               have i₂ := b5e223
               grind)
            | exact superpose b5e223 b5e1528
            | (have j0 := b5e1528 X0 y x
               grind)
            | (have r₁ := b5e1528 (M.op y y) y x
               have r₂ := b5e223
               grind)
            | exact resolve b5e1528 b5e223
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e223 b5e1528
          have b5e62385 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e62382 X0
               have j1 := b5e18 y X0
               grind)
            | (have r₁ := b5e62382 (k y y)
               have r₂ := b5e18 y y
               grind)
            | (have r₁ := b5e62382 x
               have r₂ := b5e18 y x
               grind)
            | (have r₁ := b5e62382 (M.op X0 X0)
               have r₂ := b5e18 X0 (M.op y y)
               grind)
            | exact resolve b5e62382 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62382
          have b5e64417 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) ∨ (τ X0) = (M.op (τ X0) y) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 y
               have i₂ := b5e62385 (τ X0)
               grind)
            | exact superpose b5e62385 b5e27
            | (have j1 := b5e62385 (τ X0)
               grind)
            | exact resolve b5e27 b5e62385
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e62385
          have b5e140180 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1328 y x
               grind)
            | exact superpose b5e1328 b5e24
            | (have j1 := b5e1328 y x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e1328 x y
               grind)
            | exact resolve b5e24 b5e1328
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1328
          have b5e140693 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b5e140180
               have i₂ := b5e1356
               grind)
            | exact superpose b5e1356 b5e140180
            | exact resolve b5e140180 b5e1356
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1356 b5e140180
          have b5e280861 : ∀ X0 : G, (σ (M.op y X0)) = (k (σ y) (σ X0)) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e64417 (σ X0)
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e64417
            | exact resolve b5e64417 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64417
          have b5e280935 : ∀ X0 : G, (σ (M.op y X0)) = (σ (k y X0)) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e280861 X0
               have i₂ := b5e19 y X0
               grind)
            | exact superpose b5e19 b5e280861
            | (have j0 := b5e280861 X0
               grind)
            | exact resolve b5e280861 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e280861
          have b5e426743 : (σ y) ≠ (σ (M.op y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e140693
               have i₂ := b5e280935 x
               grind)
            | exact superpose b5e280935 b5e140693
            | (have j1 := b5e280935 x
               grind)
            | exact resolve b5e140693 b5e280935
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e140693 b5e280935
          have b5e426753 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e426743
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e426743
            | exact resolve b5e426743 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e426743
          have b5e426754 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y x)) ∨ x = (M.op x y) := by grind
          clear b5e426753
          have b5e426768 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e426754
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e426754
            | exact resolve b5e426754 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e426754
          have b5e426787 : (M.op x x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e14 (M.op x x)
               have i₂ := b5e426768
               grind)
            | exact superpose b5e426768 b5e14
            | exact resolve b5e14 b5e426768
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e426768
          have b5e426832 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e426787
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e426787
            | exact resolve b5e426787 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e426787
          have b5e427032 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e1388 x y
               have i₂ := b5e426832
               grind)
            | exact superpose b5e426832 b5e1388
            | exact resolve b5e1388 b5e426832
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1388 b5e426832
          have b5e427089 : x = (M.op x x) ∨ (σ x) = (σ y) := by grind
          clear b5e427032
          have b5e427515 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e2086 X0 x x
               have i₂ := b5e427089
               grind)
            | exact superpose b5e427089 b5e2086
            | exact resolve b5e2086 b5e427089
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2086 b5e427089
          have b5e428194 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e1357
               have i₂ := b5e427515 x
               grind)
            | exact superpose b5e427515 b5e1357
            | exact resolve b5e1357 b5e427515
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e427515
          have b5e428567 : (σ x) = (σ y) := by grind
          clear b5e428194
          have b5e428946 : y = (τ (σ x)) := by
            first
            | (have i₁ := b5e14 y
               have i₂ := b5e428567
               grind)
            | exact superpose b5e428567 b5e14
            | exact resolve b5e14 b5e428567
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e428567
          have b5e429072 : x = y := by
            first
            | (have i₁ := b5e428946
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e428946
            | exact resolve b5e428946 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e428946
          have b5e429178 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1357
               have i₂ := b5e429072
               grind)
            | exact superpose b5e429072 b5e1357
            | exact resolve b5e1357 b5e429072
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1357 b5e429072
          have b5e429330 : False := by grind
          exact b5e429330
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X0) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
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
        have b6e75 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
        have b6e83 : y = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e75
             have r₂ := b6e20
             grind)
          | exact resolve b6e75 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e86 : y = (M.op x y) := by
          first
          | (have r₁ := b6e83
             have r₂ := b6e21
             grind)
          | exact resolve b6e83 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e89 : ∀ X0 : G, (M.op y x) = (M.op x (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e12 x X0 y
             have i₂ := b6e86
             grind)
          | exact superpose b6e86 b6e12
          | exact resolve b6e12 b6e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e157 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b6e89 x
             have i₂ := b6e86
             grind)
          | exact superpose b6e86 b6e89
          | exact resolve b6e89 b6e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e89
        have b6e172 : y = (M.op y x) := by
          first
          | (have i₁ := b6e157
             have i₂ := b6e86
             grind)
          | exact superpose b6e86 b6e157
          | exact resolve b6e157 b6e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86 b6e157
        have b6e178 : False := by grind
        exact b6e178
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X0) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X1 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e19
            | exact resolve b7e19 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e28 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) X3) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 (M.op X0 X2) X0
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e13 X0 X3 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e40 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e43 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e40
          have b7e44 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e43
               have r₂ := b7e23
               grind)
            | exact resolve b7e43 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e45 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
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
          have b7e51 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k X0 (τ X1))
               have i₂ := b7e27 X1 X0
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b7e59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e65 : (σ y) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e23
            | exact resolve b7e23 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e67 : (σ (k x y)) = (k (σ x) (σ (k x y))) := by grind
          have b7e70 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = (M.op X0 (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ x) (σ x)
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e13
            | exact resolve b7e13 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e71 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b7e70 X0
               have i₂ := b7e28 X0
               grind)
            | exact superpose b7e28 b7e70
            | exact resolve b7e70 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e72 : (σ (k x y)) = (σ (k x (k x y))) := by
            first
            | (have i₁ := b7e67
               have i₂ := b7e19 x (k x y)
               grind)
            | exact superpose b7e19 b7e67
            | exact resolve b7e67 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e73 : (M.op (σ x) (σ y)) = (M.op (σ (k x y)) (σ x)) := by
            first
            | (have i₁ := b7e28 (σ x)
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e28
            | exact resolve b7e28 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e78 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (σ x))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 (σ x)
               have i₂ := b7e28 X0
               grind)
            | exact superpose b7e28 b7e13
            | exact resolve b7e13 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e81 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op X1 (M.op X0 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 (M.op X0 (σ x)) X0
               have i₂ := b7e28 X0
               grind)
            | exact superpose b7e28 b7e13
            | exact resolve b7e13 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e84 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e65
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e65 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e85 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e84
               have r₂ := b7e21
               grind)
            | exact resolve b7e84 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84
          have b7e86 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have r₁ := b7e85
               have r₂ := b7e22
               grind)
            | exact resolve b7e85 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e107 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op X4 X0)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e34 X3 X4 X0 (M.op X0 X2)
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e34
            | exact resolve b7e34 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e108 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (σ y))) = (M.op X1 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e34 X1 X2 X0 (M.op X0 (σ x))
               have i₂ := b7e28 X0
               grind)
            | exact superpose b7e28 b7e34
            | exact resolve b7e34 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e542 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b7e71 X0
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e71
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e71 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e585 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op y x) := by
            intro X0
            first
            | (have j0 := b7e542 X0
               grind)
            | (have r₁ := b7e542 X0
               have r₂ := b7e21
               grind)
            | exact resolve b7e542 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e542
          have b7e587 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
            intro X0
            first
            | (have j0 := b7e585 X0
               grind)
            | (have r₁ := b7e585 X0
               have r₂ := b7e22
               grind)
            | exact resolve b7e585 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e585
          have b7e785 : (σ (M.op x y)) = (σ (k x (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e72
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e72
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e72 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e797 : (σ (M.op x y)) = (σ (k x (M.op x y))) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e785
               have r₂ := b7e21
               grind)
            | exact resolve b7e785 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e785
          have b7e798 : (σ (M.op x y)) = (σ (k x (M.op x y))) := by
            first
            | (have r₁ := b7e797
               have r₂ := b7e22
               grind)
            | exact resolve b7e797 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e797
          have b7e988 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
            intro X0
            first
            | (have i₁ := b7e78 X0 (M.op (σ x) (σ x))
               have i₂ := b7e28 (σ x)
               grind)
            | exact superpose b7e28 b7e78
            | exact resolve b7e78 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28 b7e78
          have b7e1452 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e57 x x
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e57
            | exact resolve b7e57 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1559 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by grind
          clear b7e1452
          have b7e2163 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ x) (σ y)
               have i₂ := b7e988 X0
               grind)
            | exact superpose b7e988 b7e13
            | exact resolve b7e13 b7e988
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e988
          have b7e2260 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e73
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e73
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e73 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e2296 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e2260
               have r₂ := b7e21
               grind)
            | exact resolve b7e2260 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2260
          have b7e2307 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) := by
            first
            | (have r₁ := b7e2296
               have r₂ := b7e22
               grind)
            | exact resolve b7e2296 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2296
          have b7e2324 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e2163 (σ y)
               have i₂ := b7e18 (σ y) x
               grind)
            | (have i₁ := b7e2163 X0
               have i₂ := b7e18 X0 (M.op X0 (σ y))
               grind)
            | exact superpose b7e18 b7e2163
            | (have j1 := b7e18 (σ y) X0
               grind)
            | exact resolve b7e2163 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2348 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (M.op X1 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e30 (σ y) X1 X2 X0
               have i₂ := b7e2163 X0
               grind)
            | exact superpose b7e2163 b7e30
            | exact resolve b7e30 b7e2163
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e2163
          have b7e2390 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b7e2324 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2324
          have b7e2639 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X3)) = (M.op X0 (M.op (σ y) (M.op X1 X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e108 X3 X0 X4
               have i₂ := b7e107 (σ y) X1 X2 X0 X3
               grind)
            | exact superpose b7e107 b7e108
            | exact resolve b7e108 b7e107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e107 b7e108
          have b7e2690 : ∀ X0 X3 X4 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X4 X3)) := by
            intro X0 X3 X4
            first
            | (have i₁ := b7e2639 X0 x x X3 X4
               have i₂ := b7e2348 X0 x x
               grind)
            | exact superpose b7e2348 b7e2639
            | exact resolve b7e2639 b7e2348
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2348 b7e2639
          have b7e2836 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e81 X1 X0
               have i₂ := b7e2690 X0 (σ y) X1
               grind)
            | exact superpose b7e2690 b7e81
            | exact resolve b7e81 b7e2690
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81 b7e2690
          have b7e10307 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (k x (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e57 x (M.op x y)
               have i₂ := b7e2307
               grind)
            | exact superpose b7e2307 b7e57
            | (have j0 := b7e57 x (M.op x y)
               grind)
            | exact resolve b7e57 b7e2307
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e10361 : (σ (k x (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have r₁ := b7e10307
               have r₂ := b7e20
               grind)
            | exact resolve b7e10307 b7e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10307
          have b7e10374 : (M.op (σ x) (σ y)) = (σ (k x (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e10361
               have i₂ := b7e587 (σ x)
               grind)
            | exact superpose b7e587 b7e10361
            | exact resolve b7e10361 b7e587
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e587 b7e10361
          have b7e10382 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e10374
               have i₂ := b7e798
               grind)
            | exact superpose b7e798 b7e10374
            | exact resolve b7e10374 b7e798
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e798 b7e10374
          have b7e10389 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have r₁ := b7e10382
               have r₂ := b7e20
               grind)
            | exact resolve b7e10382 b7e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10382
          have b7e10468 : (σ (M.op x y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e45
               have i₂ := b7e10389
               grind)
            | exact superpose b7e10389 b7e45
            | exact resolve b7e45 b7e10389
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10389
          have b7e10557 : (k x y) = (τ (σ (M.op x y))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e10468
               grind)
            | exact superpose b7e10468 b7e14
            | exact resolve b7e14 b7e10468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e10576 : (M.op x y) = (k x y) := by
            first
            | (have i₁ := b7e10557
               have i₂ := b7e14 (M.op x y)
               grind)
            | exact superpose b7e14 b7e10557
            | exact resolve b7e10557 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10557
          have b7e20679 : (k x y) = (τ (σ (k x x))) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e1559
               grind)
            | exact superpose b7e1559 b7e14
            | exact resolve b7e14 b7e1559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1559
          have b7e20722 : (k x y) = (k x x) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e20679
               have i₂ := b7e14 (k x x)
               grind)
            | exact superpose b7e14 b7e20679
            | exact resolve b7e20679 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e20679
          have b7e20747 : (M.op x y) = (k x x) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e20722
               have i₂ := b7e10576
               grind)
            | exact superpose b7e10576 b7e20722
            | exact resolve b7e20722 b7e10576
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10576 b7e20722
          have b7e20764 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
            first
            | (have i₁ := b7e20747
               have i₂ := b7e10468
               grind)
            | exact superpose b7e10468 b7e20747
            | exact resolve b7e20747 b7e10468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e20747
          have b7e22842 : (σ x) ≠ (σ y) ∨ (M.op x y) = (k x x) := by
            first
            | (have i₁ := b7e86
               have i₂ := b7e20764
               grind)
            | exact superpose b7e20764 b7e86
            | exact resolve b7e86 b7e20764
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86 b7e20764
          have b7e33958 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e51 y X0
               have i₂ := b7e2390 X0
               grind)
            | exact superpose b7e2390 b7e51
            | (have j1 := b7e2390 X0
               grind)
            | exact resolve b7e51 b7e2390
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51 b7e2390
          have b7e72312 : (τ (σ y)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e33958 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e33958
            | (have j0 := b7e33958 (σ x)
               grind)
            | exact resolve b7e33958 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33958
          have b7e72410 : (k y x) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e72312
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e72312
            | exact resolve b7e72312 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72312
          have b7e72438 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e72410
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e72410
            | exact resolve b7e72410 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72410
          have b7e74472 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e72438
               grind)
            | exact superpose b7e72438 b7e20
            | exact resolve b7e20 b7e72438
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e74588 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e2836 (σ x) (σ y)
               have i₂ := b7e72438
               grind)
            | exact superpose b7e72438 b7e2836
            | exact resolve b7e2836 b7e72438
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2836 b7e72438
          have b7e74594 : (σ x) = (σ (k x y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e74588
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e74588
            | exact resolve b7e74588 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74588
          have b7e74657 : (σ (M.op x y)) = (σ x) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e74594
               have i₂ := b7e10468
               grind)
            | exact superpose b7e10468 b7e74594
            | exact resolve b7e74594 b7e10468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74594
          have b7e74680 : y = (k y x) := by
            first
            | (have r₁ := b7e74657
               have r₂ := b7e74472
               grind)
            | exact resolve b7e74657 b7e74472
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74472 b7e74657
          have b7e79235 : y = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e59 x y
               have i₂ := b7e74680
               grind)
            | exact superpose b7e74680 b7e59
            | (have j0 := b7e59 y x
               grind)
            | exact resolve b7e59 b7e74680
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e79236 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e79235
               have r₂ := b7e22
               grind)
            | exact resolve b7e79235 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79235
          have b7e81707 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b7e2307
               have i₂ := b7e79236
               grind)
            | exact superpose b7e79236 b7e2307
            | exact resolve b7e2307 b7e79236
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2307 b7e79236
          have b7e81840 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = y := by
            first
            | (have i₁ := b7e81707
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e81707
            | exact resolve b7e81707 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45 b7e81707
          have b7e81865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b7e81840
               have i₂ := b7e10468
               grind)
            | exact superpose b7e10468 b7e81840
            | exact resolve b7e81840 b7e10468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10468 b7e81840
          have b7e81873 : x = y := by
            first
            | (have r₁ := b7e81865
               have r₂ := b7e20
               grind)
            | exact resolve b7e81865 b7e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81865
          have b7e85807 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e81873
               grind)
            | exact superpose b7e81873 b7e22
            | exact resolve b7e22 b7e81873
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e85865 : (σ x) ≠ (σ x) ∨ (M.op x x) = (k x x) := by
            first
            | (have i₁ := b7e22842
               have i₂ := b7e81873
               grind)
            | exact superpose b7e81873 b7e22842
            | exact resolve b7e22842 b7e81873
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e22842
          have b7e85872 : x = (k x x) := by
            first
            | (have i₁ := b7e74680
               have i₂ := b7e81873
               grind)
            | exact superpose b7e81873 b7e74680
            | exact resolve b7e74680 b7e81873
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74680 b7e81873
          have b7e85873 : (M.op x x) = (k x x) := by grind
          clear b7e85865
          have b7e85876 : x = (M.op x x) := by
            first
            | (have i₁ := b7e85873
               have i₂ := b7e85872
               grind)
            | exact superpose b7e85872 b7e85873
            | exact resolve b7e85873 b7e85872
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85872 b7e85873
          have b7e85915 : False := by grind
          exact b7e85915
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e57 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e958 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e57 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57
          have b8e959 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e958
               have r₂ := b8e24
               grind)
            | exact resolve b8e958 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e958
          have b8e960 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e959
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e959
            | exact resolve b8e959 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e959
          have b8e961 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e960
               grind)
            | exact superpose b8e960 b8e20
            | exact resolve b8e20 b8e960
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e960
          have b8e1147 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e961
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e961
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e961 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e961
          have b8e1148 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e1147
          have b8e1150 : y = (M.op y x) := by
            first
            | (have r₁ := b8e1148
               have r₂ := b8e21
               grind)
            | exact resolve b8e1148 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1148
          have b8e1152 : False := by grind
          exact b8e1152

/-- `Equation4540`: `x ◇ (y ◇ z) = (z ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_y_pxx_pxy_Equation4540 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4540 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4540.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X0) X0) := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
      have b0e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X0) X2) X2) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 X1 (M.op X3 X0)
           have i₂ := b0e11 X1 X3 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) X3) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X3 (M.op X2 X0) X0
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X3 X1)) = (M.op (M.op (M.op X0 X1) X1) (M.op X2 X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X2 X0) X3 X1
           have i₂ := b0e11 X1 X2 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 (M.op X2 X0))) = (M.op (M.op X0 (M.op X1 X2)) X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 X3 (M.op X2 X0)
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ y) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ x) X0 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op y x) := by
        intro X0
        first
        | (have i₁ := b0e11 x X0 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e11 X0 X3 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e38 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e38
        | exact resolve b0e38 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e66 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 X1
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X2 X0)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X1 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e77 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e141 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 (σ y))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e39 X1 X2 X0 (M.op (σ x) X0)
           have i₂ := b0e34 X0
           grind)
        | exact superpose b0e34 b0e39
        | exact resolve b0e39 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e143 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e39 X0 X1 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e39
        | exact resolve b0e39 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e187 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e143 X0 y
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e143
        | exact resolve b0e143 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e197 : ∀ X0 : G, (M.op (M.op x X0) X0) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 x x
           have i₂ := b0e143 X0 x
           grind)
        | exact superpose b0e143 b0e11
        | exact resolve b0e11 b0e143
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e205 : ∀ X0 X1 X2 : G, (M.op (M.op X1 x) (M.op X2 X0)) = (M.op (M.op X0 (M.op X1 x)) y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 (M.op X1 x) X2 X0
           have i₂ := b0e143 (M.op X0 (M.op X1 x)) X1
           grind)
        | exact superpose b0e143 b0e11
        | exact resolve b0e11 b0e143
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e211 : ∀ X0 X1 X2 : G, (M.op (M.op X1 x) (M.op X2 X0)) = (M.op (M.op X0 y) y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e205 X0 X1 X2
           have i₂ := b0e143 X0 X1
           grind)
        | exact superpose b0e143 b0e205
        | exact resolve b0e205 b0e143
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e205
      have b0e259 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e33 X0 x x X1
           have i₂ := b0e143 X0 x
           grind)
        | exact superpose b0e143 b0e33
        | exact resolve b0e33 b0e143
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e143
      have b0e385 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e39 X0 x y X1
           have i₂ := b0e187 X0
           grind)
        | exact superpose b0e187 b0e39
        | exact resolve b0e39 b0e187
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e187
      have b0e455 : ∀ X0 X1 : G, (M.op (M.op y X0) X0) = (M.op X0 (M.op (M.op x X1) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e32 x X1 X0 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e32
        | exact resolve b0e32 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e602 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op (M.op y X0) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e455 X0 X1
           have i₂ := b0e141 X1 X0 (M.op x X1)
           grind)
        | (have i₁ := b0e455 X1 (σ y)
           have i₂ := b0e141 (M.op x (σ y)) X1 x
           grind)
        | exact superpose b0e141 b0e455
        | exact resolve b0e455 b0e141
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e455
      have b0e651 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op X0 (M.op y y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e602 X0 X1
           have i₂ := b0e259 y X0
           grind)
        | exact superpose b0e259 b0e602
        | exact resolve b0e602 b0e259
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e602
      have b0e669 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 (σ y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e651 X0 X1
           have i₂ := b0e385 X0 y
           grind)
        | exact superpose b0e385 b0e651
        | exact resolve b0e651 b0e385
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e651
      have b0e713 : ∀ X0 X1 : G, (M.op (M.op X1 X0) y) = (M.op (M.op (M.op X0 x) x) (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e197 (M.op X1 X0)
           have i₂ := b0e11 x X1 X0
           grind)
        | exact superpose b0e11 b0e197
        | exact resolve b0e197 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e736 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e39 X1 X2 X0 (M.op x X0)
           have i₂ := b0e197 X0
           grind)
        | exact superpose b0e197 b0e39
        | exact resolve b0e39 b0e197
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e742 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) y)) := by
        first
        | (have i₁ := b0e37 (M.op x (σ x))
           have i₂ := b0e197 (σ x)
           grind)
        | exact superpose b0e197 b0e37
        | exact resolve b0e37 b0e197
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e197
      have b0e747 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op y (σ y))) := by
        first
        | (have i₁ := b0e742
           have i₂ := b0e141 y (σ x) (σ x)
           grind)
        | exact superpose b0e141 b0e742
        | exact resolve b0e742 b0e141
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141 b0e742
      have b0e751 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e736 X0 X1 X2
           have i₂ := b0e385 X1 X0
           grind)
        | exact superpose b0e385 b0e736
        | exact resolve b0e736 b0e385
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e385 b0e736
      have b0e764 : ∀ X0 X1 : G, (M.op (M.op X0 y) y) = (M.op (M.op X1 X0) y) := by
        intro X0 X1
        first
        | (have i₁ := b0e713 X0 X1
           have i₂ := b0e211 X0 (M.op X0 x) X1
           grind)
        | exact superpose b0e211 b0e713
        | exact resolve b0e713 b0e211
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e211 b0e713
      have b0e766 : (M.op (σ y) (σ x)) = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e747
           have i₂ := b0e669 (σ x) y
           grind)
        | exact superpose b0e669 b0e747
        | exact resolve b0e747 b0e669
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e669 b0e747
      have b0e773 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op (M.op X1 X0) y) := by
        intro X0 X1
        first
        | (have i₁ := b0e764 X0 X1
           have i₂ := b0e259 X0 y
           grind)
        | exact superpose b0e259 b0e764
        | exact resolve b0e764 b0e259
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e259 b0e764
      have b0e778 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op X1 X0) y) := by
        intro X0 X1
        first
        | (have i₁ := b0e773 X0 X1
           have i₂ := b0e751 y y X0
           grind)
        | exact superpose b0e751 b0e773
        | exact resolve b0e773 b0e751
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e773
      have b0e1254 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X1 X0)) = X2 ∨ (M.op (M.op X1 X0) X2) = (k (M.op X1 X0) X2) ∨ (M.op X2 (M.op X1 X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e16 (M.op X1 X0) X2
           have i₂ := b0e35 X0 X0 X1 X1
           grind)
        | (have i₁ := b0e16 (M.op (M.op X0 X0) X0) X1
           have i₂ := b0e35 X0 X0 (M.op X0 X0) x
           grind)
        | exact superpose b0e35 b0e16
        | (have j0 := b0e16 (M.op X1 X0) X2
           grind)
        | exact resolve b0e16 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e1323 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) y) = X2 ∨ (M.op (M.op X1 X0) X2) = (k (M.op X1 X0) X2) ∨ (M.op X2 (M.op X1 X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1254 X0 X1 X2
           have i₂ := b0e751 X0 (M.op (M.op X0 X0) X0) X1
           grind)
        | exact superpose b0e751 b0e1254
        | (have j0 := b0e1254 X0 X1 X2
           grind)
        | exact resolve b0e1254 b0e751
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1254
      have b0e1435 : ∀ X0 X1 X2 : G, (M.op y y) = X2 ∨ (M.op (M.op X1 X0) X2) = (k (M.op X1 X0) X2) ∨ (M.op X2 (M.op X1 X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1323 X0 X1 X2
           have i₂ := b0e778 X0 (M.op X0 X0)
           grind)
        | exact superpose b0e778 b0e1323
        | (have j0 := b0e1323 X0 X1 X2
           grind)
        | exact resolve b0e1323 b0e778
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e778 b0e1323
      have b0e1537 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (k (M.op X1 X0) X2) ∨ (M.op y y) = X2 ∨ (M.op X2 y) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1435 X0 X1 X2
           have i₂ := b0e751 X0 X2 X1
           grind)
        | exact superpose b0e751 b0e1435
        | (have j0 := b0e1435 X0 X1 X2
           grind)
        | exact resolve b0e1435 b0e751
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1435
      have b0e2053 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e66 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66
      have b0e2055 : ∀ X0 X1 : G, (M.op X1 y) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e2053 X0 X1 x
           have i₂ := b0e751 X1 X1 x
           grind)
        | exact superpose b0e751 b0e2053
        | (have j0 := b0e2053 X0 X1 x
           grind)
        | (have r₁ := b0e2053 (M.op X0 y) X0 x
           have r₂ := b0e751 X0 X0 x
           grind)
        | exact resolve b0e2053 b0e751
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2053
      have b0e2310 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e751 (σ x) X0 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e751
        | exact resolve b0e751 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2344 : ∀ X0 X2 X3 : G, (M.op X0 y) = (M.op (M.op X0 (M.op X3 X2)) X0) := by
        intro X0 X2 X3
        first
        | (have i₁ := b0e36 X0 X3 X2 x
           have i₂ := b0e751 (M.op X2 X0) X0 x
           grind)
        | exact superpose b0e751 b0e36
        | exact resolve b0e36 b0e751
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e2409 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 y) X0) := by
        intro X0
        first
        | (have i₁ := b0e2344 X0 x x
           have i₂ := b0e751 x X0 x
           grind)
        | exact superpose b0e751 b0e2344
        | exact resolve b0e2344 b0e751
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e751 b0e2344
      have b0e2879 : ∀ X0 : G, (M.op (σ y) y) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e16 (σ y) X0
           have i₂ := b0e2310 (σ y)
           grind)
        | exact superpose b0e2310 b0e16
        | (have j0 := b0e16 (σ y) X0
           grind)
        | exact resolve b0e16 b0e2310
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2907 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e2310 (σ x)
           grind)
        | exact superpose b0e2310 b0e18
        | exact resolve b0e18 b0e2310
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2936 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have j0 := b0e2879 X0
           have j1 := b0e2055 X0 (σ y)
           grind)
        | (have r₁ := b0e2879 X0
           have r₂ := b0e2055 X0 (σ y)
           grind)
        | (have r₁ := b0e2879 (M.op x y)
           have r₂ := b0e2055 (M.op (σ y) y) x
           grind)
        | (have r₁ := b0e2879 y
           have r₂ := b0e2055 (k (σ y) y) (σ y)
           grind)
        | exact resolve b0e2879 b0e2055
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2879
      have b0e2962 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e2936 X0
           have i₂ := b0e2310 X0
           grind)
        | exact superpose b0e2310 b0e2936
        | (have j0 := b0e2936 X0
           grind)
        | exact resolve b0e2936 b0e2310
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2310 b0e2936
      have b0e21605 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) ∨ (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e77 y X0
           have i₂ := b0e2962 X0
           grind)
        | exact superpose b0e2962 b0e77
        | (have j1 := b0e2962 X0
           grind)
        | exact resolve b0e77 b0e2962
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77 b0e2962
      have b0e64980 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op y y) = X0 ∨ (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e1537 x x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e1537
        | (have j0 := b0e1537 X0 x X0
           grind)
        | exact resolve b0e1537 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1537
      have b0e65015 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
        intro X0
        first
        | (have j0 := b0e64980 X0
           have j1 := b0e2055 X0 y
           grind)
        | (have r₁ := b0e64980 y
           have r₂ := b0e2055 (k y y) y
           grind)
        | (have r₁ := b0e64980 X0
           have r₂ := b0e2055 X0 y
           grind)
        | (have r₁ := b0e64980 (M.op x y)
           have r₂ := b0e2055 (M.op y y) x
           grind)
        | exact resolve b0e64980 b0e2055
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2055 b0e64980
      have b0e85862 : (τ (M.op (σ x) y)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e21605 (σ x)
           have i₂ := b0e766
           grind)
        | exact superpose b0e766 b0e21605
        | (have j0 := b0e21605 (σ x)
           grind)
        | exact resolve b0e21605 b0e766
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e766 b0e21605
      have b0e85975 : (k y x) = (τ (M.op (σ x) y)) ∨ (σ x) = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e85862
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e85862
        | exact resolve b0e85862 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e85862
      have b0e107013 : (M.op (σ x) y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e13 (M.op (σ x) y)
           have i₂ := b0e85975
           grind)
        | exact superpose b0e85975 b0e13
        | exact resolve b0e13 b0e85975
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e85975
      have b0e107730 : (M.op (σ x) y) = (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e107013
           have i₂ := b0e65015 x
           grind)
        | exact superpose b0e65015 b0e107013
        | (have j1 := b0e65015 (σ x)
           grind)
        | exact resolve b0e107013 b0e65015
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65015 b0e107013
      have b0e107797 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e107730
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e107730
        | exact resolve b0e107730 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e107730
      have b0e107818 : (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
        first
        | (have r₁ := b0e107797
           have r₂ := b0e2907
           grind)
        | exact resolve b0e107797 b0e2907
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2907 b0e107797
      have b0e110171 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e2409 (σ x)
           have i₂ := b0e107818
           grind)
        | exact superpose b0e107818 b0e2409
        | exact resolve b0e2409 b0e107818
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e107818
      have b0e110342 : x = (M.op x y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e110171
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e110171
        | exact resolve b0e110171 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e110171
      have b0e111741 : x = (M.op x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e2409 x
           have i₂ := b0e110342
           grind)
        | exact superpose b0e110342 b0e2409
        | exact resolve b0e2409 b0e110342
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2409 b0e110342
      have b0e111899 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e111741
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e111741
        | exact resolve b0e111741 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e111741
      have b0e113399 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e111899
           grind)
        | exact superpose b0e111899 b0e12
        | exact resolve b0e12 b0e111899
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e111899
      have b0e113476 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e113399
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e113399
        | exact resolve b0e113399 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e113399
      have b0e113477 : x = y := by grind
      clear b0e113476
      have b0e115655 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e113477
           grind)
        | exact superpose b0e113477 b0e18
        | exact resolve b0e18 b0e113477
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e113477
      have b0e115866 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e115655
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e115655
        | exact resolve b0e115655 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e115655
      have b0e115941 : False := by grind
      exact b0e115941
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : y = (k x y) := by grind
        have b1e46 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b1e49 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e46
        have b1e51 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e49
             have r₂ := b1e21
             grind)
          | exact resolve b1e49 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e52 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
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
        have b1e53 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e24
             grind)
          | exact superpose b1e24 b1e52
          | exact resolve b1e52 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e52
        have b1e54 : False := by grind
        exact b1e54
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X0) X0) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : y = (k x y) := by grind
        have b2e29 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b2e12 x X0 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 (M.op X2 X0))) = (M.op (M.op X0 (M.op X1 X2)) X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X0 X3 (M.op X2 X0)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e12 X0 X3 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b2e29 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e29
          | exact resolve b2e29 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e58 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 (σ x) X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e97 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e32 X0 X1 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e32
          | exact resolve b2e32 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e131 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b2e97 X0 y
             have i₂ := b2e33
             grind)
          | exact superpose b2e33 b2e97
          | exact resolve b2e97 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e140 : ∀ X0 : G, (M.op (M.op x X0) X0) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e12 X0 x x
             have i₂ := b2e97 X0 x
             grind)
          | exact superpose b2e97 b2e12
          | exact resolve b2e12 b2e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e97
        have b2e428 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 y)) := by
          intro X0 X1
          first
          | (have i₁ := b2e32 X0 x y X1
             have i₂ := b2e131 X0
             grind)
          | exact superpose b2e131 b2e32
          | exact resolve b2e32 b2e131
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e131
        have b2e814 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 X1))) = (M.op (M.op X1 (M.op X0 y)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e31 X1 (M.op x X0) X0 X2
             have i₂ := b2e140 X0
             grind)
          | exact superpose b2e140 b2e31
          | exact resolve b2e31 b2e140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e817 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e32 X1 X2 X0 (M.op x X0)
             have i₂ := b2e140 X0
             grind)
          | exact superpose b2e140 b2e32
          | exact resolve b2e32 b2e140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e140
        have b2e833 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e817 X0 X1 X2
             have i₂ := b2e428 X1 X0
             grind)
          | exact superpose b2e428 b2e817
          | exact resolve b2e817 b2e428
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e817
        have b2e836 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 X1))) = (M.op (M.op X1 y) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e814 X0 X1 X2
             have i₂ := b2e428 X1 X0
             grind)
          | exact superpose b2e428 b2e814
          | exact resolve b2e814 b2e428
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e428 b2e814
        have b2e851 : ∀ X1 : G, (M.op X1 y) = (M.op (M.op X1 y) X1) := by
          intro X1
          first
          | (have i₁ := b2e836 x X1 x
             have i₂ := b2e833 (M.op x X1) X1 x
             grind)
          | exact superpose b2e833 b2e836
          | exact resolve b2e836 b2e833
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e836
        have b2e1498 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e58 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e1499 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1498
             have r₂ := b2e22
             grind)
          | exact resolve b2e1498 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1498
        have b2e1500 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1499
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1499
          | exact resolve b2e1499 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1499
        have b2e1501 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1500
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1500
          | exact resolve b2e1500 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1500
        have b2e1514 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b2e32 X0 X1 (σ y) (σ x)
             have i₂ := b2e1501
             grind)
          | exact superpose b2e1501 b2e32
          | exact resolve b2e32 b2e1501
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e1515 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e1514 X0 x
             have i₂ := b2e833 (σ y) X0 x
             grind)
          | exact superpose b2e833 b2e1514
          | exact resolve b2e1514 b2e833
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e833 b2e1514
        have b2e2224 : (σ y) = (M.op (σ x) y) := by
          first
          | (have i₁ := b2e1501
             have i₂ := b2e1515 (σ x)
             grind)
          | exact superpose b2e1515 b2e1501
          | exact resolve b2e1501 b2e1515
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1501 b2e1515
        have b2e3476 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e851 (σ x)
             have i₂ := b2e2224
             grind)
          | exact superpose b2e2224 b2e851
          | exact resolve b2e851 b2e2224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e851 b2e2224
        have b2e3568 : False := by
          have f3568_10 : (σ y) = (M.op (σ y) (σ x)) := by grind
          have f3568_18 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have f3568_20 : False := by
            first
            | (have r₁ := f3568_10
               have r₂ := f3568_18
               grind)
            | exact resolve f3568_10 f3568_18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          exact f3568_20
        exact b2e3568
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
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
        have b3e60 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b3e61 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
        clear b3e60
        have b3e62 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e61
             have r₂ := b3e20
             grind)
          | exact resolve b3e61 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61
        have b3e63 : y = (M.op x x) := by
          first
          | (have i₁ := b3e62
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e62
          | exact resolve b3e62 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e62
        have b3e64 : False := by grind
        exact b3e64
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X0) X0) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X0) X2) X2) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 X1 (M.op X3 X0)
               have i₂ := b4e13 X1 X3 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e30 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 : G, (M.op y x) = (M.op x (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e13 x X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X0 X1 X2
               have i₂ := b4e13 X0 X3 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 : G, y = (M.op x (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e34 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e34
            | exact resolve b4e34 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e37 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e33 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e33
            | exact resolve b4e33 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e110 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X0 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op (σ x) X0) X0
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e13
            | exact resolve b4e13 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e112 : y = (M.op x (M.op y (σ y))) := by
            first
            | (have i₁ := b4e36 (M.op (σ x) y)
               have i₂ := b4e30 y
               grind)
            | exact superpose b4e30 b4e36
            | exact resolve b4e36 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e145 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 (σ y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e35 X1 X2 X0 (M.op (σ x) X0)
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e35
            | exact resolve b4e35 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e148 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (M.op X2 (σ y)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e35 X0 X1 (M.op X2 (σ y)) (σ x)
               have i₂ := b4e37 X2
               grind)
            | exact superpose b4e37 b4e35
            | exact resolve b4e35 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e175 : ∀ X0 : G, y = (M.op x (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e112
               have i₂ := b4e35 x y (σ y) X0
               grind)
            | (have i₁ := b4e112
               have i₂ := b4e35 x X0 (σ y) y
               grind)
            | exact superpose b4e35 b4e112
            | exact resolve b4e112 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112
          have b4e188 : ∀ X0 : G, y = (M.op (M.op X0 x) x) := by
            intro X0
            first
            | (have i₁ := b4e175 X0
               have i₂ := b4e110 X0 x
               grind)
            | exact superpose b4e110 b4e175
            | exact resolve b4e175 b4e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e110 b4e175
          have b4e207 : y = (M.op x (σ y)) := by
            first
            | (have i₁ := b4e30 x
               have i₂ := b4e188 (σ x)
               grind)
            | exact superpose b4e188 b4e30
            | exact resolve b4e30 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30
          have b4e208 : ∀ X0 X1 : G, y = (M.op x (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 x X0 X1
               have i₂ := b4e188 X1
               grind)
            | exact superpose b4e188 b4e13
            | exact resolve b4e13 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e188
          have b4e304 : (σ y) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e37 x
               have i₂ := b4e207
               grind)
            | exact superpose b4e207 b4e37
            | exact resolve b4e37 b4e207
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e309 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b4e35 X0 X1 (σ y) x
               have i₂ := b4e207
               grind)
            | exact superpose b4e207 b4e35
            | exact resolve b4e35 b4e207
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e207
          have b4e403 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X0 X1) X2) X2)) = (M.op X3 (M.op X4 (M.op (M.op X1 X5) X5))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e35 X3 X4 (M.op (M.op X1 X5) X5) X2
               have i₂ := b4e28 X1 X5 X2 X0
               grind)
            | exact superpose b4e28 b4e35
            | exact resolve b4e35 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e35
          have b4e404 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X0 X1) X2) X2)) = (M.op X3 (M.op X4 (M.op X5 (σ y)))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e403 X0 X1 X2 X3 X4 X5
               have i₂ := b4e145 X5 X4 (M.op X1 X5)
               grind)
            | (have i₁ := b4e403 X0 X1 X2 X3 X1 (σ y)
               have i₂ := b4e145 (M.op X1 (σ y)) X1 X2
               grind)
            | exact superpose b4e145 b4e403
            | exact resolve b4e403 b4e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e403
          have b4e474 : ∀ X0 X1 X2 X3 : G, (M.op X3 (σ y)) = (M.op X3 (M.op (M.op (M.op X0 X1) X2) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e404 X0 X1 X2 X3 x x
               have i₂ := b4e148 X3 x x
               grind)
            | exact superpose b4e148 b4e404
            | exact resolve b4e404 b4e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e148 b4e404
          have b4e514 : ∀ X2 X3 : G, (M.op X3 (σ y)) = (M.op X3 (M.op X2 (σ y))) := by
            intro X2 X3
            first
            | (have i₁ := b4e474 x x X2 X3
               have i₂ := b4e145 X2 X3 (M.op (M.op x x) X2)
               grind)
            | (have i₁ := b4e474 x x (σ y) x
               have i₂ := b4e145 (M.op (M.op x x) (σ y)) x X2
               grind)
            | exact superpose b4e145 b4e474
            | exact resolve b4e474 b4e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e145 b4e474
          have b4e540 : ∀ X3 : G, (M.op X3 (σ y)) = (M.op X3 y) := by
            intro X3
            first
            | (have i₁ := b4e514 x X3
               have i₂ := b4e309 X3 x
               grind)
            | exact superpose b4e309 b4e514
            | exact resolve b4e514 b4e309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e309 b4e514
          have b4e584 : y = (M.op x y) := by
            first
            | (have i₁ := b4e208 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e208
            | exact resolve b4e208 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e208
          have b4e1701 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e540 (σ x)
               grind)
            | exact superpose b4e540 b4e20
            | exact resolve b4e20 b4e540
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e540
          have b4e1750 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e1701
               have i₂ := b4e304
               grind)
            | exact superpose b4e304 b4e1701
            | exact resolve b4e1701 b4e304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e304 b4e1701
          have b4e1773 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e1750
               have i₂ := b4e584
               grind)
            | exact superpose b4e584 b4e1750
            | exact resolve b4e1750 b4e584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e584 b4e1750
          have b4e1774 : False := by grind
          exact b4e1774
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X0) X0) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X0) X2) X2) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 X1 (M.op X3 X0)
               have i₂ := b5e13 X1 X3 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) X3) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X3 (M.op X2 X0) X0
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 : G, (M.op y x) = (M.op x (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e13 x X0 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X3 X1)) = (M.op (M.op (M.op X0 X1) X1) (M.op X2 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X2 X0) X3 X1
               have i₂ := b5e13 X1 X2 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e13 X0 X3 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 : G, y = (M.op x (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e30 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e30
            | exact resolve b5e30 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e46 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
          have b5e47 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
          clear b5e46
          have b5e48 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e47
               have r₂ := b5e21
               grind)
            | exact resolve b5e47 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e54 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e56 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 X1
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X2 X0)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X1 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e57 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X1) X1) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 X2
               have i₂ := b5e18 X2 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X1 X2)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X2 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e58 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ x) X0
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 (σ x) X0
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e101 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 (M.op X1 (M.op X2 y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33 X0 X1 (M.op X2 y) x
               have i₂ := b5e34 X2
               grind)
            | exact superpose b5e34 b5e33
            | exact resolve b5e33 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e102 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 x)) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 X0 X1 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e33
            | exact resolve b5e33 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e133 : ∀ X0 : G, (M.op (M.op x X0) X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x x
               have i₂ := b5e102 X0 x
               grind)
            | exact superpose b5e102 b5e13
            | exact resolve b5e13 b5e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e135 : ∀ X0 : G, (M.op (M.op X0 x) y) = (k (M.op X0 x) (M.op (M.op X0 x) y)) := by
            intro X0
            grind
          have b5e141 : ∀ X0 X1 X2 : G, (M.op (M.op X1 x) (M.op X2 X0)) = (M.op (M.op X0 (M.op X1 x)) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op X1 x) X2 X0
               have i₂ := b5e102 (M.op X0 (M.op X1 x)) X1
               grind)
            | exact superpose b5e102 b5e13
            | exact resolve b5e13 b5e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e142 : ∀ X0 X1 X2 : G, (M.op (M.op X1 x) (M.op X2 X0)) = (M.op (M.op X0 y) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e141 X0 X1 X2
               have i₂ := b5e102 X0 X1
               grind)
            | exact superpose b5e102 b5e141
            | exact resolve b5e141 b5e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e141
          have b5e178 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X0 y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e29 X0 x x X1
               have i₂ := b5e102 X0 x
               grind)
            | exact superpose b5e102 b5e29
            | exact resolve b5e29 b5e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e102
          have b5e229 : ∀ X0 X1 : G, (M.op (M.op X1 X0) y) = (M.op (M.op (M.op X0 x) x) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e133 (M.op X1 X0)
               have i₂ := b5e13 x X1 X0
               grind)
            | exact superpose b5e13 b5e133
            | exact resolve b5e133 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e245 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33 X1 X2 X0 (M.op x X0)
               have i₂ := b5e133 X0
               grind)
            | exact superpose b5e133 b5e33
            | exact resolve b5e33 b5e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e133
          have b5e259 : ∀ X0 X1 : G, (M.op (M.op X0 y) y) = (M.op (M.op X1 X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b5e229 X0 X1
               have i₂ := b5e142 X0 (M.op X0 x) X1
               grind)
            | exact superpose b5e142 b5e229
            | exact resolve b5e229 b5e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e142 b5e229
          have b5e265 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op (M.op X1 X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b5e259 X0 X1
               have i₂ := b5e178 X0 y
               grind)
            | exact superpose b5e178 b5e259
            | exact resolve b5e259 b5e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e259
          have b5e348 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X2) = (M.op X2 (M.op X4 X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e33 X2 (M.op X1 X3) X3 X4
               have i₂ := b5e28 X1 X3 X2 X0
               grind)
            | exact superpose b5e28 b5e33
            | exact resolve b5e33 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e353 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X3) X3) (M.op X4 X2)) = (M.op (M.op (M.op (M.op X0 X1) X2) X2) (M.op (M.op X1 X3) X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 (M.op (M.op X1 X3) X3) X4 X2
               have i₂ := b5e28 X1 X3 X2 X0
               grind)
            | exact superpose b5e28 b5e13
            | exact resolve b5e13 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e358 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X0 X1) X2) X2)) = (M.op X3 (M.op X4 (M.op (M.op X1 X5) X5))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e33 X3 X4 (M.op (M.op X1 X5) X5) X2
               have i₂ := b5e28 X1 X5 X2 X0
               grind)
            | exact superpose b5e28 b5e33
            | exact resolve b5e33 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e359 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X0 X1) X2) X2)) = (M.op X3 (M.op X4 (M.op X5 y))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e358 X0 X1 X2 X3 X4 X5
               have i₂ := b5e245 X5 X4 (M.op X1 X5)
               grind)
            | (have i₁ := b5e358 X0 X1 X2 X3 X1 y
               have i₂ := b5e245 (M.op X1 y) X1 X2
               grind)
            | exact superpose b5e245 b5e358
            | exact resolve b5e358 b5e245
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e358
          have b5e363 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X3) X3) (M.op X4 X2)) = (M.op (M.op (M.op (M.op X0 X1) X2) X2) (M.op X3 y)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e353 X0 X1 X2 X3 X4
               have i₂ := b5e245 X3 (M.op (M.op (M.op X0 X1) X2) X2) (M.op X1 X3)
               grind)
            | (have i₁ := b5e353 X0 X1 X2 y X4
               have i₂ := b5e245 (M.op X1 y) (M.op (M.op (M.op X0 X1) X2) X2) X2
               grind)
            | exact superpose b5e245 b5e353
            | exact resolve b5e353 b5e245
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e353
          have b5e366 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 X1) y)) = (M.op X2 (M.op X4 X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e348 X0 X1 X2 X3 X4
               have i₂ := b5e178 (M.op X0 X1) X2
               grind)
            | exact superpose b5e178 b5e348
            | exact resolve b5e348 b5e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e348
          have b5e410 : ∀ X0 X1 X2 X3 : G, (M.op X3 y) = (M.op X3 (M.op (M.op (M.op X0 X1) X2) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e359 X0 X1 X2 X3 x x
               have i₂ := b5e101 X3 x x
               grind)
            | exact superpose b5e101 b5e359
            | exact resolve b5e359 b5e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e101 b5e359
          have b5e414 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X3) X3) (M.op X4 X2)) = (M.op (M.op X2 (M.op (M.op X0 X1) y)) (M.op X3 y)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e363 X0 X1 X2 X3 X4
               have i₂ := b5e178 (M.op X0 X1) X2
               grind)
            | exact superpose b5e178 b5e363
            | exact resolve b5e363 b5e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e363
          have b5e417 : ∀ X2 X3 X4 : G, (M.op X2 (M.op X4 X3)) = (M.op X2 (M.op y y)) := by
            intro X2 X3 X4
            first
            | (have i₁ := b5e366 x x X2 X3 X4
               have i₂ := b5e245 y X2 (M.op x x)
               grind)
            | (have i₁ := b5e366 x x x X3 X4
               have i₂ := b5e245 (M.op x x) x X2
               grind)
            | exact superpose b5e245 b5e366
            | exact resolve b5e366 b5e245
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e366
          have b5e450 : ∀ X2 X3 : G, (M.op X3 y) = (M.op X3 (M.op X2 y)) := by
            intro X2 X3
            first
            | (have i₁ := b5e410 x x X2 X3
               have i₂ := b5e245 X2 X3 (M.op (M.op x x) X2)
               grind)
            | (have i₁ := b5e410 x x y x
               have i₂ := b5e245 (M.op (M.op x x) y) x X2
               grind)
            | exact superpose b5e245 b5e410
            | exact resolve b5e410 b5e245
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e410
          have b5e454 : ∀ X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X3) X3) (M.op X4 X2)) = (M.op (M.op X2 (M.op y y)) (M.op X3 y)) := by
            intro X1 X2 X3 X4
            first
            | (have i₁ := b5e414 x X1 X2 X3 X4
               have i₂ := b5e245 y X2 (M.op x X1)
               grind)
            | (have i₁ := b5e414 x X1 X1 X3 X4
               have i₂ := b5e245 (M.op x X1) X1 X2
               grind)
            | exact superpose b5e245 b5e414
            | exact resolve b5e414 b5e245
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e245 b5e414
          have b5e464 : ∀ X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X3) X3) (M.op X4 X2)) = (M.op (M.op X2 (M.op y y)) y) := by
            intro X1 X2 X3 X4
            first
            | (have i₁ := b5e454 X1 X2 X3 X4
               have i₂ := b5e450 X3 (M.op X2 (M.op y y))
               grind)
            | exact superpose b5e450 b5e454
            | exact resolve b5e454 b5e450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e454
          have b5e470 : ∀ X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X3) X3) (M.op X4 X2)) = (M.op y (M.op (M.op y y) y)) := by
            intro X1 X2 X3 X4
            first
            | (have i₁ := b5e464 X1 X2 X3 X4
               have i₂ := b5e265 (M.op y y) X2
               grind)
            | exact superpose b5e265 b5e464
            | exact resolve b5e464 b5e265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e265 b5e464
          have b5e475 : ∀ X1 X2 X3 X4 : G, (M.op (M.op y y) y) = (M.op (M.op (M.op X1 X3) X3) (M.op X4 X2)) := by
            intro X1 X2 X3 X4
            first
            | (have i₁ := b5e470 X1 X2 X3 X4
               have i₂ := b5e13 y (M.op y y) y
               grind)
            | exact superpose b5e13 b5e470
            | exact resolve b5e470 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e470
          have b5e479 : ∀ X1 X2 X3 X4 : G, (M.op (M.op y y) y) = (M.op (M.op X3 (M.op X1 y)) (M.op X4 X2)) := by
            intro X1 X2 X3 X4
            first
            | (have i₁ := b5e475 X1 X2 X3 X4
               have i₂ := b5e178 X1 X3
               grind)
            | exact superpose b5e178 b5e475
            | exact resolve b5e475 b5e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e475
          have b5e483 : ∀ X2 X3 X4 : G, (M.op (M.op y y) y) = (M.op (M.op X3 y) (M.op X4 X2)) := by
            intro X2 X3 X4
            first
            | (have i₁ := b5e479 x X2 X3 X4
               have i₂ := b5e450 x X3
               grind)
            | exact superpose b5e450 b5e479
            | exact resolve b5e479 b5e450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e479
          have b5e487 : ∀ X2 X3 X4 : G, (M.op y (M.op y y)) = (M.op (M.op X3 y) (M.op X4 X2)) := by
            intro X2 X3 X4
            first
            | (have i₁ := b5e483 X2 X3 X4
               have i₂ := b5e178 y y
               grind)
            | exact superpose b5e178 b5e483
            | exact resolve b5e483 b5e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e483
          have b5e490 : ∀ X2 X3 X4 : G, (M.op y y) = (M.op (M.op X3 y) (M.op X4 X2)) := by
            intro X2 X3 X4
            first
            | (have i₁ := b5e487 X2 X3 X4
               have i₂ := b5e450 y y
               grind)
            | exact superpose b5e450 b5e487
            | exact resolve b5e487 b5e450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e487
          have b5e509 : y = (M.op x y) := by
            first
            | (have i₁ := b5e34 x
               have i₂ := b5e450 x x
               grind)
            | exact superpose b5e450 b5e34
            | exact resolve b5e34 b5e450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e1048 : ∀ X0 X1 : G, (M.op (M.op X1 X0) y) = (M.op (M.op (M.op X0 y) y) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e450 x (M.op X1 X0)
               have i₂ := b5e31 X0 y X1 x
               grind)
            | (have i₁ := b5e450 x (M.op (M.op y X1) X1)
               have i₂ := b5e31 y X1 x x
               grind)
            | exact superpose b5e31 b5e450
            | exact resolve b5e450 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1051 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X1 X0)) = X2 ∨ (M.op (M.op X1 X0) X2) = (k (M.op X1 X0) X2) ∨ (M.op X2 (M.op X1 X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e18 (M.op X1 X0) X2
               have i₂ := b5e31 X0 X0 X1 X1
               grind)
            | (have i₁ := b5e18 (M.op (M.op X0 X0) X0) X1
               have i₂ := b5e31 X0 X0 (M.op X0 X0) x
               grind)
            | exact superpose b5e31 b5e18
            | (have j0 := b5e18 (M.op X1 X0) X2
               grind)
            | exact resolve b5e18 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1052 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X1 X0)) = (k (M.op X1 X0) (M.op (M.op (M.op X0 X0) X0) (M.op X1 X0))) := by
            intro X0 X1
            grind
          have b5e1069 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X1 X3) X3) (M.op X4 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e33 (M.op (M.op X1 X3) X3) X0 X1 X4
               have i₂ := b5e31 X1 X3 X0 X2
               grind)
            | (have i₁ := b5e33 (M.op X2 X0) X3 X1 X3
               have i₂ := b5e31 X0 X1 X2 X3
               grind)
            | exact superpose b5e31 b5e33
            | exact resolve b5e33 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e1107 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X3 (M.op X1 y)) (M.op X4 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e1069 X0 X1 X2 X3 X4
               have i₂ := b5e178 X1 X3
               grind)
            | exact superpose b5e178 b5e1069
            | exact resolve b5e1069 b5e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1069
          have b5e1120 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 y)) (M.op X1 X0)) = (k (M.op X1 X0) (M.op (M.op X0 (M.op X0 y)) (M.op X1 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e1052 X1 X1
               have i₂ := b5e178 X1 X1
               grind)
            | exact superpose b5e178 b5e1052
            | exact resolve b5e1052 b5e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1052
          have b5e1121 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 y)) (M.op X1 X0)) = X2 ∨ (M.op (M.op X1 X0) X2) = (k (M.op X1 X0) X2) ∨ (M.op X2 (M.op X1 X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1051 X0 X1 X2
               have i₂ := b5e178 X0 X0
               grind)
            | exact superpose b5e178 b5e1051
            | (have j0 := b5e1051 X0 X1 X2
               grind)
            | exact resolve b5e1051 b5e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1051
          have b5e1124 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op X1 X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b5e1048 X0 X1
               have i₂ := b5e490 X0 (M.op X0 y) X1
               grind)
            | exact superpose b5e490 b5e1048
            | exact resolve b5e1048 b5e490
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1048
          have b5e1214 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X3 y) (M.op X4 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e1107 X0 X1 X2 X3 X4
               have i₂ := b5e450 X1 X3
               grind)
            | exact superpose b5e450 b5e1107
            | exact resolve b5e1107 b5e450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1107
          have b5e1224 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op X1 X0)) = (k (M.op X1 X0) (M.op (M.op X0 y) (M.op X1 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e1120 x X1
               have i₂ := b5e450 x x
               grind)
            | exact superpose b5e450 b5e1120
            | exact resolve b5e1120 b5e450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1120
          have b5e1225 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) (M.op X1 X0)) = X2 ∨ (M.op (M.op X1 X0) X2) = (k (M.op X1 X0) X2) ∨ (M.op X2 (M.op X1 X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1121 X0 X1 X2
               have i₂ := b5e450 X0 X0
               grind)
            | exact superpose b5e450 b5e1121
            | (have j0 := b5e1121 X0 X1 X2
               grind)
            | exact resolve b5e1121 b5e450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1121
          have b5e1299 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op y y) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e1214 X0 X1 X2 X3 x
               have i₂ := b5e490 X1 X3 x
               grind)
            | exact superpose b5e490 b5e1214
            | exact resolve b5e1214 b5e490
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1214
          have b5e1306 : ∀ X0 X1 : G, (M.op y y) = (k (M.op X1 X0) (M.op y y)) := by
            intro X0 X1
            by_contra hcon
            push Not at hcon
            have f1306_15 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op X1 X0)) = (k (M.op X1 X0) (M.op (M.op X0 y) (M.op X1 X0))) := by
              intro X0 X1
              grind
            have f1306_16 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op (M.op X1 y) (M.op X2 X0)) := by
              intro X0 X1 X2
              grind
            have f1306_28 : (M.op y y) ≠ (k (M.op X1 X0) (M.op y y)) := by grind
            have f1306_30 : ∀ X0 X1 : G, (M.op y y) = (k (M.op X1 X0) (M.op y y)) := by
              intro X0 X1
              first
              | (have i₁ := f1306_15 X0 x
                 have i₂ := f1306_16 X0 X0 x
                 grind)
              | exact superpose f1306_16 f1306_15
              | exact resolve f1306_15 f1306_16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f1306_77 : (M.op y y) ≠ (M.op y y) := by
              first
              | (have i₁ := f1306_28
                 have i₂ := f1306_30 X0 X1
                 grind)
              | exact superpose f1306_30 f1306_28
              | (have r₁ := f1306_28
                 have r₂ := f1306_30 X0 X1
                 grind)
              | exact resolve f1306_28 f1306_30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f1306_78 : False := by grind
            exact f1306_78
          clear b5e1224
          have b5e1307 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (k (M.op X1 X0) X2) ∨ (M.op y y) = X2 ∨ (M.op X2 (M.op X1 X0)) = X2 := by
            intro X0 X1 X2
            by_contra hcon
            push Not at hcon
            obtain ⟨g0, g1, g2⟩ := hcon
            have f1307_17 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) (M.op X1 X0)) = X2 ∨ (M.op (M.op X1 X0) X2) = (k (M.op X1 X0) X2) ∨ (M.op X2 (M.op X1 X0)) = X2 := by
              intro X0 X1 X2
              grind
            have f1307_18 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op (M.op X1 y) (M.op X2 X0)) := by
              intro X0 X1 X2
              grind
            have f1307_30 : (M.op (M.op X1 X0) X2) ≠ (k (M.op X1 X0) X2) := by grind
            have f1307_31 : (M.op y y) ≠ X2 := by grind
            have f1307_32 : X2 ≠ (M.op X2 (M.op X1 X0)) := by grind
            have f1307_34 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (k (M.op X1 X0) X2) ∨ (M.op y y) = X2 ∨ (M.op X2 (M.op X1 X0)) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := f1307_17 X0 X1 X2
                 have i₂ := f1307_18 X0 X0 X1
                 grind)
              | exact superpose f1307_18 f1307_17
              | (have j0 := f1307_17 X0 X1 X2
                 grind)
              | exact resolve f1307_17 f1307_18
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f1307_116 : (M.op (M.op X1 X0) X2) ≠ (M.op (M.op X1 X0) X2) ∨ (M.op y y) = X2 ∨ X2 = (M.op X2 (M.op X1 X0)) := by
              first
              | (have i₁ := f1307_30
                 have i₂ := f1307_34 X0 X1 X2
                 grind)
              | exact superpose f1307_34 f1307_30
              | (have j1 := f1307_34 X0 X1 X2
                 grind)
              | (have r₁ := f1307_30
                 have r₂ := f1307_34 X0 X1 X2
                 grind)
              | exact resolve f1307_30 f1307_34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f1307_118 : (M.op y y) = X2 ∨ X2 = (M.op X2 (M.op X1 X0)) := by grind
            have f1307_120 : X2 = (M.op X2 (M.op X1 X0)) := by
              first
              | (have r₁ := f1307_118
                 have r₂ := f1307_31
                 grind)
              | exact resolve f1307_118 f1307_31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f1307_122 : False := by
              first
              | (have r₁ := f1307_120
                 have r₂ := f1307_32
                 grind)
              | exact resolve f1307_120 f1307_32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            exact f1307_122
          clear b5e490 b5e1225
          have b5e1542 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e54 (σ X1) (σ X0)
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e54
            | (have j0 := b5e54 (σ X1) (σ X0)
               grind)
            | exact resolve b5e54 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e1627 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e58 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e1628 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1627
               have r₂ := b5e24
               grind)
            | exact resolve b5e1627 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1627
          have b5e1629 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1628
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1628
            | exact resolve b5e1628 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1628
          have b5e1630 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1629
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e1629
            | exact resolve b5e1629 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1629
          have b5e1810 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e56 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e2253 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op X3 X0)) ∨ (M.op X4 X1) = (k X4 X1) ∨ (M.op X1 X4) = X1 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e33 X2 X3 X0 (M.op X4 X0)
               have i₂ := b5e57 X1 X0 X4
               grind)
            | exact superpose b5e57 b5e33
            | (have j1 := b5e57 X1 X1 X4
               grind)
            | exact resolve b5e33 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33 b5e57
          have b5e2904 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e52 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e2905 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e2904 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2904
          have b5e3085 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X0 (σ (M.op x x)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e29 X0 (σ x) (σ y) X1
               have i₂ := b5e1630
               grind)
            | exact superpose b5e1630 b5e29
            | exact resolve b5e29 b5e1630
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e3104 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 (M.op y y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e3085 X0 X1
               have i₂ := b5e417 X1 (σ (M.op x x)) X0
               grind)
            | exact superpose b5e417 b5e3085
            | exact resolve b5e3085 b5e417
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e417 b5e3085
          have b5e3117 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b5e3104 X0 X1
               have i₂ := b5e450 y X1
               grind)
            | exact superpose b5e450 b5e3104
            | exact resolve b5e3104 b5e450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e450 b5e3104
          have b5e3494 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e3117 X2 X0
               grind)
            | exact superpose b5e3117 b5e13
            | exact resolve b5e13 b5e3117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3117
          have b5e27296 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e2905 (M.op y y)
               have i₂ := b5e1306 y y
               grind)
            | exact superpose b5e1306 b5e2905
            | (have j0 := b5e2905 (M.op y y)
               grind)
            | exact resolve b5e2905 b5e1306
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1306 b5e2905
          have b5e27302 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
          clear b5e27296
          have b5e27391 : (M.op y y) = (M.op (σ (M.op y y)) y) := by
            first
            | (have i₁ := b5e1124 (σ (M.op y y)) (σ (M.op y y))
               have i₂ := b5e27302
               grind)
            | exact superpose b5e27302 b5e1124
            | exact resolve b5e1124 b5e27302
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1124
          have b5e27399 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b5e3494 X0 (σ (M.op y y)) (σ (M.op y y))
               have i₂ := b5e27302
               grind)
            | exact superpose b5e27302 b5e3494
            | exact resolve b5e3494 b5e27302
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32790 : (σ (M.op y y)) = (M.op (σ (M.op y y)) y) := by
            first
            | (have i₁ := b5e27302
               have i₂ := b5e27399 (σ (M.op y y))
               grind)
            | exact superpose b5e27399 b5e27302
            | exact resolve b5e27302 b5e27399
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27302 b5e27399
          have b5e32981 : (M.op y y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e32790
               have i₂ := b5e27391
               grind)
            | exact superpose b5e27391 b5e32790
            | exact resolve b5e32790 b5e27391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27391 b5e32790
          have b5e57676 : ∀ X0 X1 X3 : G, (M.op y y) ≠ X3 ∨ (k (M.op X0 X1) X3) = (M.op (M.op X0 X1) X3) ∨ (M.op X3 (M.op X0 X1)) = X3 := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e1810 X3 (M.op X0 X1) x
               have i₂ := b5e1299 X0 X1 x (M.op X0 X1)
               grind)
            | exact superpose b5e1299 b5e1810
            | (have j0 := b5e1810 X3 (M.op X0 X1) x
               grind)
            | (have r₁ := b5e1810 (M.op y y) (M.op X0 X1) x
               have r₂ := b5e1299 X0 X1 x (M.op X0 X1)
               grind)
            | exact resolve b5e1810 b5e1299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1299 b5e1810
          have b5e57691 : ∀ X0 X1 X3 : G, (k (M.op X0 X1) X3) = (M.op (M.op X0 X1) X3) ∨ (M.op X3 (M.op X0 X1)) = X3 := by
            intro X0 X1 X3
            first
            | (have j0 := b5e57676 X0 X1 X3
               have j1 := b5e1307 X1 X0 X3
               grind)
            | (have r₁ := b5e57676 X0 X1 x
               have r₂ := b5e1307 X0 X1 x
               grind)
            | (have r₁ := b5e57676 X0 X1 (M.op y y)
               have r₂ := b5e1307 X0 X1 (M.op y y)
               grind)
            | (have r₁ := b5e57676 X0 X1 (M.op (M.op y y) (M.op X1 X0))
               have r₂ := b5e1307 X0 X1 (M.op y y)
               grind)
            | exact resolve b5e57676 b5e1307
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1307 b5e57676
          have b5e57815 : ∀ X0 X1 X3 : G, (k (M.op X0 X1) X3) = (M.op (M.op X0 X1) X3) ∨ (M.op X3 y) = X3 := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e57691 X0 X1 X3
               have i₂ := b5e3494 X3 X0 X1
               grind)
            | exact superpose b5e3494 b5e57691
            | (have j0 := b5e57691 X0 X1 X3
               grind)
            | exact resolve b5e57691 b5e3494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57691
          have b5e93955 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X1)) ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (k (M.op X1 X0) X0) ∨ (M.op X0 (M.op X1 X0)) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e2253 X0 X0 X2 x (M.op X1 X0)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2253
          have b5e93960 : ∀ X0 X1 : G, (M.op X0 y) ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (k (M.op X1 X0) X0) ∨ (M.op X0 (M.op X1 X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e93955 X0 X1 x
               have i₂ := b5e3494 X0 x X1
               grind)
            | exact superpose b5e3494 b5e93955
            | (have j0 := b5e93955 X0 X1 x
               grind)
            | exact resolve b5e93955 b5e3494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e93955
          have b5e94675 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (k (M.op X1 X0) X0) ∨ (M.op X0 (M.op X1 X0)) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e93960 X0 X1
               have j1 := b5e57815 X1 X0 X0
               grind)
            | (have r₁ := b5e93960 x X1
               have r₂ := b5e57815 X0 X1 x
               grind)
            | exact resolve b5e93960 b5e57815
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57815 b5e93960
          have b5e95155 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (k (M.op X1 X0) X0) ∨ (M.op X0 (M.op X1 X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e94675 X0 X1
               have i₂ := b5e178 X1 X0
               grind)
            | exact superpose b5e178 b5e94675
            | (have j0 := b5e94675 X0 X1
               grind)
            | exact resolve b5e94675 b5e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e178 b5e94675
          have b5e95508 : ∀ X0 X1 : G, (M.op X0 y) = (k (M.op X1 X0) X0) ∨ (M.op X0 (M.op X1 X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e95155 X0 X1
               have i₂ := b5e3494 X0 X1 y
               grind)
            | exact superpose b5e3494 b5e95155
            | (have j0 := b5e95155 X0 X1
               grind)
            | exact resolve b5e95155 b5e3494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95155
          have b5e95705 : ∀ X0 X1 : G, (M.op X0 y) = (k (M.op X1 X0) X0) ∨ (M.op X0 y) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e95508 X0 X1
               have i₂ := b5e3494 X0 X1 X0
               grind)
            | exact superpose b5e3494 b5e95508
            | (have j0 := b5e95508 X0 X1
               grind)
            | exact resolve b5e95508 b5e3494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3494 b5e95508
          have b5e95937 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e95705 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e95705
            | (have j0 := b5e95705 x x
               grind)
            | exact resolve b5e95705 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95705
          have b5e95992 : y = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e95937
               have i₂ := b5e509
               grind)
            | exact superpose b5e509 b5e95937
            | exact resolve b5e95937 b5e509
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95937
          have b5e96094 : y = (k y x) ∨ x = y := by
            first
            | (have i₁ := b5e95992
               have i₂ := b5e509
               grind)
            | exact superpose b5e509 b5e95992
            | exact resolve b5e95992 b5e509
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95992
          have b5e101597 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1542 y x
               grind)
            | exact superpose b5e1542 b5e24
            | (have j1 := b5e1542 y x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e1542 x y
               grind)
            | exact resolve b5e24 b5e1542
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1542
          have b5e102062 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b5e101597
               have i₂ := b5e1630
               grind)
            | exact superpose b5e1630 b5e101597
            | exact resolve b5e101597 b5e1630
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e101597
          have b5e312688 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e102062
               have i₂ := b5e96094
               grind)
            | exact superpose b5e96094 b5e102062
            | exact resolve b5e102062 b5e96094
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e96094 b5e102062
          have b5e312700 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
          clear b5e312688
          have b5e312757 : (M.op x x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e14 (M.op x x)
               have i₂ := b5e312700
               grind)
            | exact superpose b5e312700 b5e14
            | exact resolve b5e14 b5e312700
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e312700
          have b5e312808 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e312757
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e312757
            | exact resolve b5e312757 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e312757
          have b5e312887 : (M.op x y) = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e135 x
               have i₂ := b5e312808
               grind)
            | exact superpose b5e312808 b5e135
            | exact resolve b5e135 b5e312808
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e135 b5e312808
          have b5e313091 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e312887
               have i₂ := b5e509
               grind)
            | exact superpose b5e509 b5e312887
            | exact resolve b5e312887 b5e509
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e312887
          have b5e313141 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e313091
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e313091
            | exact resolve b5e313091 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e313091
          have b5e313170 : (σ x) = (σ y) ∨ x = y := by
            first
            | (have r₁ := b5e313141
               have r₂ := b5e21
               grind)
            | exact resolve b5e313141 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e313141
          have b5e313246 : y = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e14 y
               have i₂ := b5e313170
               grind)
            | exact superpose b5e313170 b5e14
            | exact resolve b5e14 b5e313170
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e313170
          have b5e313346 : x = y ∨ x = y := by
            first
            | (have i₁ := b5e313246
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e313246
            | exact resolve b5e313246 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e313246
          have b5e313347 : x = y := by grind
          clear b5e313346
          have b5e313388 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e313347
               grind)
            | exact superpose b5e313347 b5e20
            | exact resolve b5e20 b5e313347
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e313417 : x = (M.op x x) := by
            first
            | (have i₁ := b5e509
               have i₂ := b5e313347
               grind)
            | exact superpose b5e313347 b5e509
            | exact resolve b5e509 b5e313347
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e509
          have b5e313427 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1630
               have i₂ := b5e313347
               grind)
            | exact superpose b5e313347 b5e1630
            | exact resolve b5e1630 b5e313347
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1630
          have b5e313456 : (M.op x x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e32981
               have i₂ := b5e313347
               grind)
            | exact superpose b5e313347 b5e32981
            | exact resolve b5e32981 b5e313347
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32981 b5e313347
          have b5e313591 : (M.op x x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e313427
               have i₂ := b5e313456
               grind)
            | exact superpose b5e313456 b5e313427
            | exact resolve b5e313427 b5e313456
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e313427
          have b5e313617 : (M.op x x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e313388
               have i₂ := b5e313456
               grind)
            | exact superpose b5e313456 b5e313388
            | exact resolve b5e313388 b5e313456
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e313388 b5e313456
          have b5e313628 : x = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e313591
               have i₂ := b5e313417
               grind)
            | exact superpose b5e313417 b5e313591
            | exact resolve b5e313591 b5e313417
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e313591
          have b5e313645 : x ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e313617
               have i₂ := b5e313417
               grind)
            | exact superpose b5e313417 b5e313617
            | exact resolve b5e313617 b5e313417
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e313417 b5e313617
          have b5e313659 : False := by grind
          exact b5e313659
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X0) X0) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
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
        have b6e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) X3) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X3 (M.op X2 X0) X0
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e45 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X0 X1 X2
             have i₂ := b6e12 X0 X3 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e75 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
        have b6e83 : y = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e75
             have r₂ := b6e20
             grind)
          | exact resolve b6e75 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e86 : y = (M.op x y) := by
          first
          | (have r₁ := b6e83
             have r₂ := b6e21
             grind)
          | exact resolve b6e83 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e129 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b6e45 X0 X1 y x
             have i₂ := b6e86
             grind)
          | exact superpose b6e86 b6e45
          | exact resolve b6e45 b6e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45
        have b6e198 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X0 y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e41 X0 x y X1
             have i₂ := b6e86
             grind)
          | exact superpose b6e86 b6e41
          | exact resolve b6e41 b6e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e238 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b6e198 X0 X1
             have i₂ := b6e129 X1 X0
             grind)
          | exact superpose b6e129 b6e198
          | exact resolve b6e198 b6e129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e129 b6e198
        have b6e358 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 y) X0) := by
          intro X0
          first
          | (have i₁ := b6e238 (M.op x X0) X0
             have i₂ := b6e238 x X0
             grind)
          | exact superpose b6e238 b6e238
          | exact resolve b6e238 b6e238
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e238
        have b6e1593 : y = (M.op y x) := by
          first
          | (have i₁ := b6e358 x
             have i₂ := b6e86
             grind)
          | exact superpose b6e86 b6e358
          | exact resolve b6e358 b6e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86 b6e358
        have b6e1660 : False := by grind
        exact b6e1660
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X0) X0) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X1 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e19
            | exact resolve b7e19 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e28 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X0) X2) X2) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 X1 (M.op X3 X0)
               have i₂ := b7e13 X1 X3 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) X3) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 (M.op X2 X0) X0
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e31 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ x) X0 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e13 X0 X3 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b7e31 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e31
            | exact resolve b7e31 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e41 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e44 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e41
          have b7e45 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e44
               have r₂ := b7e23
               grind)
            | exact resolve b7e44 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e46 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
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
          have b7e52 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k X0 (τ X1))
               have i₂ := b7e27 X1 X0
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b7e60 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e77 : (σ y) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e46
               grind)
            | exact superpose b7e46 b7e23
            | exact resolve b7e23 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e79 : (σ (k x y)) = (k (σ x) (σ (k x y))) := by grind
          have b7e82 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op X0 (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ x) (σ x)
               have i₂ := b7e46
               grind)
            | exact superpose b7e46 b7e13
            | exact resolve b7e13 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e83 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b7e82 X0
               have i₂ := b7e28 X0
               grind)
            | exact superpose b7e28 b7e82
            | exact resolve b7e82 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82
          have b7e84 : (σ (k x y)) = (σ (k x (k x y))) := by
            first
            | (have i₁ := b7e79
               have i₂ := b7e19 x (k x y)
               grind)
            | exact superpose b7e19 b7e79
            | exact resolve b7e79 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79
          have b7e85 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e77
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e77
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e77 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e86 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e85
               have r₂ := b7e21
               grind)
            | exact resolve b7e85 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e87 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have r₁ := b7e86
               have r₂ := b7e22
               grind)
            | exact resolve b7e86 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e93 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (σ x))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 (σ x)
               have i₂ := b7e28 X0
               grind)
            | exact superpose b7e28 b7e13
            | exact resolve b7e13 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e95 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (σ x) X0))) = (M.op (M.op X0 (σ y)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 (M.op (σ x) X0)
               have i₂ := b7e28 X0
               grind)
            | exact superpose b7e28 b7e13
            | exact resolve b7e13 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e96 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 (M.op X0 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 (M.op (σ x) X0) X0
               have i₂ := b7e28 X0
               grind)
            | exact superpose b7e28 b7e13
            | exact resolve b7e13 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e98 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op X0 (σ y)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e95 X0 X1
               have i₂ := b7e30 X1 (σ x) X0 X0
               grind)
            | exact superpose b7e30 b7e95
            | exact resolve b7e95 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e95
          have b7e119 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (M.op X2 (σ y)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e34 X0 X1 (M.op X2 (σ y)) (σ x)
               have i₂ := b7e35 X2
               grind)
            | exact superpose b7e35 b7e34
            | exact resolve b7e34 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e125 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 (σ y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e34 X1 X2 X0 (M.op (σ x) X0)
               have i₂ := b7e28 X0
               grind)
            | exact superpose b7e28 b7e34
            | exact resolve b7e34 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e339 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X0 X1) X2) X2)) = (M.op X3 (M.op X4 (M.op (M.op X1 X5) X5))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b7e34 X3 X4 (M.op (M.op X1 X5) X5) X2
               have i₂ := b7e29 X1 X5 X2 X0
               grind)
            | exact superpose b7e29 b7e34
            | exact resolve b7e34 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e340 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X0 X1) X2) X2)) = (M.op X3 (M.op X4 (M.op X5 (σ y)))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b7e339 X0 X1 X2 X3 X4 X5
               have i₂ := b7e125 X5 X4 (M.op X1 X5)
               grind)
            | (have i₁ := b7e339 X0 X1 X2 X3 X1 (σ y)
               have i₂ := b7e125 (M.op X1 (σ y)) X1 X2
               grind)
            | exact superpose b7e125 b7e339
            | exact resolve b7e339 b7e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e339
          have b7e402 : ∀ X0 X1 X2 X3 : G, (M.op X3 (σ y)) = (M.op X3 (M.op (M.op (M.op X0 X1) X2) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e340 X0 X1 X2 X3 x x
               have i₂ := b7e119 X3 x x
               grind)
            | exact superpose b7e119 b7e340
            | exact resolve b7e340 b7e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e119 b7e340
          have b7e424 : ∀ X2 X3 : G, (M.op X3 (σ y)) = (M.op X3 (M.op X2 (σ y))) := by
            intro X2 X3
            first
            | (have i₁ := b7e402 x x X2 X3
               have i₂ := b7e125 X2 X3 (M.op (M.op x x) X2)
               grind)
            | (have i₁ := b7e402 x x (σ y) x
               have i₂ := b7e125 (M.op (M.op x x) (σ y)) x X2
               grind)
            | exact superpose b7e125 b7e402
            | exact resolve b7e402 b7e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e125 b7e402
          have b7e764 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b7e83 X0
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e83
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e83 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e773 : (M.op (σ (k x y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (k x y))) := by
            first
            | (have i₁ := b7e28 (σ (k x y))
               have i₂ := b7e83 (σ x)
               grind)
            | exact superpose b7e83 b7e28
            | exact resolve b7e28 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e809 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ (k x y)) (σ y)) := by
            first
            | (have i₁ := b7e773
               have i₂ := b7e83 (M.op (σ x) (σ y))
               grind)
            | exact superpose b7e83 b7e773
            | exact resolve b7e773 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83 b7e773
          have b7e817 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op y x) := by
            intro X0
            first
            | (have j0 := b7e764 X0
               grind)
            | (have r₁ := b7e764 X0
               have r₂ := b7e21
               grind)
            | exact resolve b7e764 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e764
          have b7e831 : (M.op (σ (k x y)) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b7e809
               have i₂ := b7e96 (σ x) (σ y)
               grind)
            | exact superpose b7e96 b7e809
            | exact resolve b7e809 b7e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e809
          have b7e837 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
            intro X0
            first
            | (have j0 := b7e817 X0
               grind)
            | (have r₁ := b7e817 X0
               have r₂ := b7e22
               grind)
            | exact resolve b7e817 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e817
          have b7e848 : (M.op (σ y) (σ y)) = (M.op (σ (k x y)) (σ y)) := by
            first
            | (have i₁ := b7e831
               have i₂ := b7e424 (σ x) (σ y)
               grind)
            | exact superpose b7e424 b7e831
            | exact resolve b7e831 b7e424
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e831
          have b7e1324 : (σ (M.op x y)) = (σ (k x (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e84
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e84
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e84 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84
          have b7e1336 : (σ (M.op x y)) = (σ (k x (M.op x y))) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e1324
               have r₂ := b7e21
               grind)
            | exact resolve b7e1324 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1324
          have b7e1337 : (σ (M.op x y)) = (σ (k x (M.op x y))) := by
            first
            | (have r₁ := b7e1336
               have r₂ := b7e22
               grind)
            | exact resolve b7e1336 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1336
          have b7e1601 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X1 X2) X0) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e29 X2 (σ x) X0 X1
               have i₂ := b7e93 X0 (M.op X2 (σ x))
               grind)
            | exact superpose b7e93 b7e29
            | exact resolve b7e29 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29 b7e93
          have b7e1655 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b7e1601 X0 x x
               have i₂ := b7e98 X0 (M.op x x)
               grind)
            | exact superpose b7e98 b7e1601
            | exact resolve b7e1601 b7e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98 b7e1601
          have b7e1981 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e35 x
               have i₂ := b7e424 x (σ x)
               grind)
            | exact superpose b7e424 b7e35
            | exact resolve b7e35 b7e424
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e424
          have b7e2300 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e58 x x
               have i₂ := b7e46
               grind)
            | exact superpose b7e46 b7e58
            | exact resolve b7e58 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2401 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by grind
          clear b7e2300
          have b7e2915 : (M.op (σ (k x y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b7e96 (σ x) (σ x)
               have i₂ := b7e46
               grind)
            | exact superpose b7e46 b7e96
            | exact resolve b7e96 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96
          have b7e3141 : (σ y) = (M.op (σ (k x y)) (σ x)) := by
            first
            | (have i₁ := b7e2915
               have i₂ := b7e35 (σ x)
               grind)
            | exact superpose b7e35 b7e2915
            | exact resolve b7e2915 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35 b7e2915
          have b7e3841 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e3141
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e3141
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e3141 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3141
          have b7e3880 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e3841
               have r₂ := b7e21
               grind)
            | exact resolve b7e3841 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3841
          have b7e3891 : (σ y) = (M.op (σ (M.op x y)) (σ x)) := by
            first
            | (have r₁ := b7e3880
               have r₂ := b7e22
               grind)
            | exact resolve b7e3880 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3880
          have b7e5211 : (σ (M.op x y)) = (σ y) ∨ (σ (k x (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e58 x (M.op x y)
               have i₂ := b7e3891
               grind)
            | exact superpose b7e3891 b7e58
            | (have j0 := b7e58 x (M.op x y)
               grind)
            | exact resolve b7e58 b7e3891
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e5248 : (σ (k x (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have r₁ := b7e5211
               have r₂ := b7e87
               grind)
            | exact resolve b7e5211 b7e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87 b7e5211
          have b7e5258 : (M.op (σ x) (σ y)) = (σ (k x (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e5248
               have i₂ := b7e837 (σ x)
               grind)
            | exact superpose b7e837 b7e5248
            | exact resolve b7e5248 b7e837
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e837 b7e5248
          have b7e5264 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e5258
               have i₂ := b7e1337
               grind)
            | exact superpose b7e1337 b7e5258
            | exact resolve b7e5258 b7e1337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1337 b7e5258
          have b7e5268 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have r₁ := b7e5264
               have r₂ := b7e20
               grind)
            | exact resolve b7e5264 b7e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5264
          have b7e5404 : (σ (M.op x y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e5268
               grind)
            | exact superpose b7e5268 b7e46
            | exact resolve b7e46 b7e5268
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46 b7e5268
          have b7e5739 : (k x y) = (τ (σ (M.op x y))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e5404
               grind)
            | exact superpose b7e5404 b7e14
            | exact resolve b7e14 b7e5404
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e5758 : (M.op x y) = (k x y) := by
            first
            | (have i₁ := b7e5739
               have i₂ := b7e14 (M.op x y)
               grind)
            | exact superpose b7e14 b7e5739
            | exact resolve b7e5739 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5739
          have b7e5994 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1655 (σ y)
               have i₂ := b7e18 (σ y) x
               grind)
            | (have i₁ := b7e1655 X0
               have i₂ := b7e18 X0 (M.op X0 (σ y))
               grind)
            | exact superpose b7e18 b7e1655
            | (have j1 := b7e18 (σ y) X0
               grind)
            | exact resolve b7e1655 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1655
          have b7e6089 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b7e5994 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5994
          have b7e21324 : (k x y) = (τ (σ (k x x))) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e2401
               grind)
            | exact superpose b7e2401 b7e14
            | exact resolve b7e14 b7e2401
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2401
          have b7e21363 : (k x y) = (k x x) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e21324
               have i₂ := b7e14 (k x x)
               grind)
            | exact superpose b7e14 b7e21324
            | exact resolve b7e21324 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21324
          have b7e21389 : (M.op x y) = (k x x) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e21363
               have i₂ := b7e5758
               grind)
            | exact superpose b7e5758 b7e21363
            | exact resolve b7e21363 b7e5758
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5758 b7e21363
          have b7e21406 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
            first
            | (have i₁ := b7e21389
               have i₂ := b7e5404
               grind)
            | exact superpose b7e5404 b7e21389
            | exact resolve b7e21389 b7e5404
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5404 b7e21389
          have b7e21759 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) := by
            first
            | (have i₁ := b7e3891
               have i₂ := b7e21406
               grind)
            | exact superpose b7e21406 b7e3891
            | exact resolve b7e3891 b7e21406
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21406
          have b7e21798 : (M.op x y) = (k x x) := by
            first
            | (have r₁ := b7e21759
               have r₂ := b7e23
               grind)
            | exact resolve b7e21759 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21759
          have b7e47463 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e52 y X0
               have i₂ := b7e6089 X0
               grind)
            | exact superpose b7e6089 b7e52
            | (have j1 := b7e6089 X0
               grind)
            | exact resolve b7e52 b7e6089
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52 b7e6089
          have b7e64450 : (τ (σ y)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e47463 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e47463
            | (have j0 := b7e47463 (σ x)
               grind)
            | exact resolve b7e47463 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47463
          have b7e64527 : (k y x) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e64450
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e64450
            | exact resolve b7e64450 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64450
          have b7e64560 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e64527
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e64527
            | exact resolve b7e64527 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64527
          have b7e64586 : y = (k y x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e64560
               have i₂ := b7e1981
               grind)
            | exact superpose b7e1981 b7e64560
            | exact resolve b7e64560 b7e1981
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1981 b7e64560
          have b7e67078 : y = (M.op y x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e60 x y
               have i₂ := b7e64586
               grind)
            | exact superpose b7e64586 b7e60
            | (have j0 := b7e60 y x
               grind)
            | exact resolve b7e60 b7e64586
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60 b7e64586
          have b7e67079 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e67078
               have r₂ := b7e22
               grind)
            | exact resolve b7e67078 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67078
          have b7e71067 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e3891
               have i₂ := b7e67079
               grind)
            | exact superpose b7e67079 b7e3891
            | exact resolve b7e3891 b7e67079
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67079
          have b7e71229 : (σ x) = (σ y) ∨ x = y := by
            first
            | (have r₁ := b7e71067
               have r₂ := b7e23
               grind)
            | exact resolve b7e71067 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71067
          have b7e75540 : y = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e71229
               grind)
            | exact superpose b7e71229 b7e14
            | exact resolve b7e14 b7e71229
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71229
          have b7e75584 : x = y ∨ x = y := by
            first
            | (have i₁ := b7e75540
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e75540
            | exact resolve b7e75540 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75540
          have b7e75585 : x = y := by grind
          clear b7e75584
          have b7e78652 : (M.op (σ x) (σ x)) = (M.op (σ (k x x)) (σ x)) := by
            first
            | (have i₁ := b7e848
               have i₂ := b7e75585
               grind)
            | exact superpose b7e75585 b7e848
            | exact resolve b7e848 b7e75585
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e848 b7e75585
          have b7e78707 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ x)) := by
            first
            | (have i₁ := b7e78652
               have i₂ := b7e21798
               grind)
            | exact superpose b7e21798 b7e78652
            | exact resolve b7e78652 b7e21798
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21798 b7e78652
          have b7e78746 : (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e78707
               have i₂ := b7e3891
               grind)
            | exact superpose b7e3891 b7e78707
            | exact resolve b7e78707 b7e3891
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3891 b7e78707
          have b7e78773 : False := by grind
          exact b7e78773
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e57 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1045 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e57 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57
          have b8e1046 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1045
               have r₂ := b8e24
               grind)
            | exact resolve b8e1045 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1045
          have b8e1047 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1046
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1046
            | exact resolve b8e1046 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1046
          have b8e1048 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1047
               grind)
            | exact superpose b8e1047 b8e20
            | exact resolve b8e20 b8e1047
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1047
          have b8e1230 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e1048
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1048
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1048 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1048
          have b8e1231 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e1230
          have b8e1233 : y = (M.op y x) := by
            first
            | (have r₁ := b8e1231
               have r₂ := b8e21
               grind)
            | exact resolve b8e1231 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1231
          have b8e1235 : False := by grind
          exact b8e1235

/-- `Equation4559`: `x ◇ (y ◇ z) = (w ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_y_pxx_pxy_Equation4559 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4559 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4559.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X3 X0) X2) := by
        intro X0 X1 X2 X3
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
      have b0e34 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ x)) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 (σ x) (σ x) X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ x) X0 X1 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 x X0 X1 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 X1 X2 x
           have i₂ := b0e11 X0 X3 X2 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : (M.op y (σ x)) = (M.op x (σ y)) := by
        first
        | (have i₁ := b0e40 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e40
        | exact resolve b0e40 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e48 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e40 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e40
        | exact resolve b0e40 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e49 : ∀ X0 X1 : G, (M.op y (M.op X1 X0)) = (M.op x (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e40 x (M.op X1 X0)
           have i₂ := b0e40 X1 X0
           grind)
        | exact superpose b0e40 b0e40
        | exact resolve b0e40 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X2 X3)) = (M.op (M.op y X0) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X1 X0) X2 X3 x
           have i₂ := b0e40 X1 X0
           grind)
        | exact superpose b0e40 b0e11
        | exact resolve b0e11 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e53 : ∀ X0 X1 : G, (M.op y X0) = (M.op y (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e49 X0 X1
           have i₂ := b0e40 y X0
           grind)
        | exact superpose b0e40 b0e49
        | exact resolve b0e49 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49
      have b0e57 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X3 X0) ∨ (M.op X3 X0) = (M.op X2 X2) ∨ (M.op X2 X2) = (k X2 (M.op X3 X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e15 X2 (M.op X3 X0)
           have i₂ := b0e11 X0 X1 X2 X3
           grind)
        | exact superpose b0e11 b0e15
        | (have j0 := b0e15 X2 (M.op X3 X0)
           grind)
        | (have r₁ := b0e15 X2 (M.op (M.op X1 X2) (M.op X1 X2))
           have r₂ := b0e11 (M.op X1 X2) X1 X2 (M.op X1 X2)
           grind)
        | exact resolve b0e15 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e66 : (M.op x y) = (M.op x (M.op x y)) := by
        first
        | (have i₁ := b0e40 y x
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e40
        | exact resolve b0e40 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e67 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 x X0 X1 y
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e11
        | exact resolve b0e11 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48
      have b0e68 : ∀ X1 : G, (M.op y X1) = (M.op (M.op x y) X1) := by
        intro X1
        first
        | (have i₁ := b0e67 x X1
           have i₂ := b0e40 x X1
           grind)
        | exact superpose b0e40 b0e67
        | exact resolve b0e67 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67
      have b0e69 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e66
           have i₂ := b0e40 x y
           grind)
        | exact superpose b0e40 b0e66
        | exact resolve b0e66 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e66
      have b0e76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
      have b0e79 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e82 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X0 X3) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 X2 X3 X1
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2 X3
           have i₂ := b0e16 X0 (M.op X3 X0)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X1 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e87 : (M.op x y) = (k y (M.op x y)) := by grind
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
      have b0e112 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e34 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e34
        | exact resolve b0e34 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e117 : (M.op (σ x) (σ y)) = (M.op (M.op x (σ y)) (σ x)) := by
        first
        | (have i₁ := b0e34 (σ x) y
           have i₂ := b0e47
           grind)
        | exact superpose b0e47 b0e34
        | exact resolve b0e34 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e128 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e117
           have i₂ := b0e34 (σ y) x
           grind)
        | exact superpose b0e34 b0e117
        | exact resolve b0e117 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117
      have b0e287 : ∀ X0 X1 : G, (M.op (σ x) (M.op y X0)) = (M.op (σ y) (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e39 y (M.op X1 X0)
           have i₂ := b0e53 X0 X1
           grind)
        | exact superpose b0e53 b0e39
        | exact resolve b0e39 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e308 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e287 X0 X1
           have i₂ := b0e39 y X0
           grind)
        | exact superpose b0e39 b0e287
        | exact resolve b0e287 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e287
      have b0e380 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e41 X0 X1 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e41
        | exact resolve b0e41 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e511 : ∀ X0 X2 : G, (M.op X0 y) = (M.op (M.op X2 X0) x) := by
        intro X0 X2
        first
        | (have i₁ := b0e11 X0 x x X2
           have i₂ := b0e380 X0 x
           grind)
        | exact superpose b0e380 b0e11
        | exact resolve b0e11 b0e380
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e380
      have b0e847 : (M.op y (M.op x y)) = (k (M.op x y) (M.op y (M.op x y))) := by grind
      clear b0e68
      have b0e872 : (M.op y y) = (k (M.op x y) (M.op y y)) := by
        first
        | (have i₁ := b0e847
           have i₂ := b0e53 y x
           grind)
        | exact superpose b0e53 b0e847
        | exact resolve b0e847 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53 b0e847
      have b0e880 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
        first
        | (have i₁ := b0e872
           have i₂ := b0e69
           grind)
        | exact superpose b0e69 b0e872
        | exact resolve b0e872 b0e69
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69 b0e872
      have b0e2850 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e79 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79
      have b0e3931 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e82 X0 X1 X2 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e82
      have b0e4692 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
        intro X0 X1
        first
        | (have j0 := b0e57 X1 X1 (M.op X0 X1) X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57
      have b0e4693 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op y X1) X1) ∨ (M.op X1 X1) = (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e4692 X0 X1
           have i₂ := b0e52 X1 X0 X0 X1
           grind)
        | exact superpose b0e52 b0e4692
        | (have j0 := b0e4692 X0 X1
           grind)
        | exact resolve b0e4692 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4692
      have b0e4755 : ∀ X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op y X1) X1)) ∨ (M.op X1 X1) = (M.op (M.op y X1) X1) := by
        intro X1
        first
        | (have i₁ := b0e4693 x X1
           have i₂ := b0e52 X1 x x X1
           grind)
        | exact superpose b0e52 b0e4693
        | (have j0 := b0e4693 x X1
           grind)
        | exact resolve b0e4693 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52 b0e4693
      have b0e5376 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e76 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76
      have b0e5377 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e5376 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5376
      have b0e19709 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e5377 (M.op x y)
           have i₂ := b0e880
           grind)
        | exact superpose b0e880 b0e5377
        | (have j0 := b0e5377 (M.op x y)
           grind)
        | exact resolve b0e5377 b0e880
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e880 b0e5377
      have b0e19718 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
      clear b0e19709
      have b0e19940 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ x)) := by
        first
        | (have i₁ := b0e34 (σ (M.op x y)) (σ (M.op x y))
           have i₂ := b0e19718
           grind)
        | exact superpose b0e19718 b0e34
        | exact resolve b0e34 b0e19718
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e19948 : (M.op (σ y) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e39 (σ (M.op x y)) (σ (M.op x y))
           have i₂ := b0e19718
           grind)
        | exact superpose b0e19718 b0e39
        | exact resolve b0e39 b0e19718
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e19718
      have b0e24304 : ∀ X1 : G, (M.op (σ y) (σ y)) ≠ X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
        intro X1
        first
        | (have i₁ := b0e3931 X1 (σ y) x
           have i₂ := b0e308 (σ y) x
           grind)
        | exact superpose b0e308 b0e3931
        | (have j0 := b0e3931 X1 (σ y) x
           grind)
        | (have r₁ := b0e3931 (M.op (σ y) (M.op X1 (M.op x (σ y)))) (σ y) x
           have r₂ := b0e308 (M.op x (σ y)) X1
           grind)
        | (have r₁ := b0e3931 (M.op (σ y) (σ y)) (σ y) X1
           have r₂ := b0e308 (σ y) X1
           grind)
        | exact resolve b0e3931 b0e308
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e308 b0e3931
      have b0e24312 : ∀ X1 : G, (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
        intro X1
        first
        | (have j0 := b0e24304 X1
           have j1 := b0e16 (σ y) X1
           grind)
        | (have r₁ := b0e24304 (k (σ y) (σ y))
           have r₂ := b0e16 (σ y) (σ y)
           grind)
        | (have r₁ := b0e24304 X1
           have r₂ := b0e16 (σ y) X1
           grind)
        | (have r₁ := b0e24304 (M.op x x)
           have r₂ := b0e16 x (M.op (σ y) (σ y))
           grind)
        | exact resolve b0e24304 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24304
      have b0e24758 : (M.op x x) = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e4755 x
           have i₂ := b0e511 x y
           grind)
        | exact superpose b0e511 b0e4755
        | exact resolve b0e4755 b0e511
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e511 b0e4755
      have b0e24845 : y = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e24758
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e24758
        | exact resolve b0e24758 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24758
      have b0e24874 : y = (k x (M.op x y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e24845
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e24845
        | exact resolve b0e24845 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24845
      have b0e30396 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) ∨ (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e98 y X0
           have i₂ := b0e24312 X0
           grind)
        | exact superpose b0e24312 b0e98
        | (have j1 := b0e24312 X0
           grind)
        | exact resolve b0e98 b0e24312
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e98 b0e24312
      have b0e32271 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e15 (σ y) (σ (M.op x y))
           have i₂ := b0e19940
           grind)
        | exact superpose b0e19940 b0e15
        | (have j0 := b0e15 (σ y) (σ (M.op x y))
           grind)
        | exact resolve b0e15 b0e19940
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e32271
           have i₂ := b0e128
           grind)
        | exact superpose b0e128 b0e32271
        | exact resolve b0e32271 b0e128
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32271
      have b0e32445 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) := by
        first
        | (have r₁ := b0e32398
           have r₂ := b0e18
           grind)
        | exact resolve b0e32398 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32398
      have b0e32454 : (M.op (σ y) (σ y)) = (σ (k y (M.op x y))) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) := by
        first
        | (have i₁ := b0e32445
           have i₂ := b0e17 y (M.op x y)
           grind)
        | exact superpose b0e17 b0e32445
        | exact resolve b0e32445 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32445
      have b0e32455 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) := by
        first
        | (have i₁ := b0e32454
           have i₂ := b0e87
           grind)
        | exact superpose b0e87 b0e32454
        | exact resolve b0e32454 b0e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32454
      have b0e32456 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) := by
        first
        | (have i₁ := b0e32455
           have i₂ := b0e128
           grind)
        | exact superpose b0e128 b0e32455
        | exact resolve b0e32455 b0e128
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e128 b0e32455
      have b0e32457 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ x)) := by
        first
        | (have r₁ := b0e32456
           have r₂ := b0e18
           grind)
        | exact resolve b0e32456 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32456
      have b0e63037 : (k y (τ (σ (M.op x y)))) = (τ (M.op (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
        first
        | (have i₁ := b0e30396 (σ (M.op x y))
           have i₂ := b0e19948
           grind)
        | exact superpose b0e19948 b0e30396
        | (have j0 := b0e30396 (σ (M.op x y))
           grind)
        | exact resolve b0e30396 b0e19948
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19948 b0e30396
      have b0e63160 : (k y (M.op x y)) = (τ (M.op (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
        first
        | (have i₁ := b0e63037
           have i₂ := b0e12 (M.op x y)
           grind)
        | exact superpose b0e12 b0e63037
        | exact resolve b0e63037 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63037
      have b0e63194 : (M.op x y) = (τ (M.op (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
        first
        | (have i₁ := b0e63160
           have i₂ := b0e87
           grind)
        | exact superpose b0e87 b0e63160
        | exact resolve b0e63160 b0e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87 b0e63160
      have b0e63212 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (M.op (σ x) (σ (M.op x y)))) := by
        first
        | (have i₁ := b0e63194
           have i₂ := b0e19940
           grind)
        | exact superpose b0e19940 b0e63194
        | exact resolve b0e63194 b0e19940
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19940 b0e63194
      have b0e63216 : (M.op x y) = (τ (M.op (σ x) (σ (M.op x y)))) := by
        first
        | (have r₁ := b0e63212
           have r₂ := b0e32457
           grind)
        | exact resolve b0e63212 b0e32457
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63212
      have b0e63278 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e13 (M.op (σ x) (σ (M.op x y)))
           have i₂ := b0e63216
           grind)
        | exact superpose b0e63216 b0e13
        | exact resolve b0e13 b0e63216
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63216
      have b0e63505 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
        first
        | (have i₁ := b0e2850 (σ x) (σ (M.op x y))
           have i₂ := b0e63278
           grind)
        | exact superpose b0e63278 b0e2850
        | (have j0 := b0e2850 (σ x) (σ (M.op x y))
           grind)
        | (have r₁ := b0e2850 (σ x) (σ (M.op x y))
           have r₂ := b0e63278
           grind)
        | exact resolve b0e2850 b0e63278
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2850
      have b0e63525 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by grind
      clear b0e63505
      have b0e63530 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
        first
        | (have r₁ := b0e63525
           have r₂ := b0e32457
           grind)
        | exact resolve b0e63525 b0e32457
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63525
      have b0e63542 : (σ (M.op x y)) = (σ (k x (M.op x y))) := by
        first
        | (have i₁ := b0e63530
           have i₂ := b0e17 x (M.op x y)
           grind)
        | exact superpose b0e17 b0e63530
        | exact resolve b0e63530 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63530
      have b0e63790 : (τ (σ (M.op x y))) = (k x (M.op x y)) := by
        first
        | (have i₁ := b0e12 (k x (M.op x y))
           have i₂ := b0e63542
           grind)
        | exact superpose b0e63542 b0e12
        | exact resolve b0e12 b0e63542
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63542
      have b0e63844 : (M.op x y) = (k x (M.op x y)) := by
        first
        | (have i₁ := b0e63790
           have i₂ := b0e12 (M.op x y)
           grind)
        | exact superpose b0e12 b0e63790
        | exact resolve b0e63790 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63790
      have b0e64613 : y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e24874
           have i₂ := b0e63844
           grind)
        | exact superpose b0e63844 b0e24874
        | exact resolve b0e24874 b0e63844
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24874 b0e63844
      have b0e64625 : y = (M.op x y) := by grind
      clear b0e64613
      have b0e64897 : (σ y) ≠ (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e32457
           have i₂ := b0e64625
           grind)
        | exact superpose b0e64625 b0e32457
        | exact resolve b0e32457 b0e64625
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32457
      have b0e64899 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e63278
           have i₂ := b0e64625
           grind)
        | exact superpose b0e64625 b0e63278
        | exact resolve b0e63278 b0e64625
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63278 b0e64625
      have b0e65013 : (σ y) ≠ (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e64897
           have i₂ := b0e112
           grind)
        | exact superpose b0e112 b0e64897
        | exact resolve b0e64897 b0e112
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e112 b0e64897
      have b0e65019 : False := by grind
      exact b0e65019
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : y = (k x y) := by grind
        have b1e53 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b1e56 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e53
        have b1e58 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e56
             have r₂ := b1e21
             grind)
          | exact resolve b1e56 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e61 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e58
          | exact resolve b1e58 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e63 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e61
             have i₂ := b1e24
             grind)
          | exact superpose b1e24 b1e61
          | exact resolve b1e61 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e61
        have b1e64 : False := by grind
        exact b1e64
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : y = (k x y) := by grind
        have b2e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b2e75 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 (σ x) X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3192 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e75 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75
        have b2e3193 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e3192
             have r₂ := b2e22
             grind)
          | exact resolve b2e3192 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3192
        have b2e3194 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e3193
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e3193
          | exact resolve b2e3193 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3193
        have b2e3195 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e3194
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e3194
          | exact resolve b2e3194 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e3194
        have b2e4604 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e67 x x
             grind)
          | exact superpose b2e67 b2e21
          | (have j1 := b2e67 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e67 x y
             grind)
          | exact resolve b2e21 b2e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e4724 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e4604
        have b2e15892 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e4724
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e4724
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e4724 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4724
        have b2e15893 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e15892
        have b2e15894 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e15893
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15893
          | exact resolve b2e15893 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15893
        have b2e15895 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e15894
        have b2e15901 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e15895
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15895
          | exact resolve b2e15895 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15895
        have b2e15910 : (σ x) ≠ (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e15901
             grind)
          | exact superpose b2e15901 b2e21
          | exact resolve b2e21 b2e15901
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e15913 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by grind
        clear b2e15901
        have b2e15962 : (σ x) = (σ (k x x)) ∨ x = y := by
          first
          | (have i₁ := b2e15913
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e15913
          | exact resolve b2e15913 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15913
        have b2e17051 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e15962
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e15962
          | (have j1 := b2e17 x x
             grind)
          | exact resolve b2e15962 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15962
        have b2e17073 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) := by grind
        clear b2e17051
        have b2e17087 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e17073
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e17073
          | exact resolve b2e17073 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17073
        have b2e17091 : x = y ∨ x = (M.op x x) := by
          first
          | (have r₁ := b2e17087
             have r₂ := b2e15910
             grind)
          | exact resolve b2e17087 b2e15910
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15910 b2e17087
        have b2e17095 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e17091
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e17091
          | exact resolve b2e17091 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17091
        have b2e17096 : x = y := by grind
        clear b2e17095
        have b2e17205 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e17096
             grind)
          | exact superpose b2e17096 b2e22
          | exact resolve b2e22 b2e17096
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e17222 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e3195
             have i₂ := b2e17096
             grind)
          | exact superpose b2e17096 b2e3195
          | exact resolve b2e3195 b2e17096
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3195 b2e17096
        have b2e17232 : False := by grind
        exact b2e17232
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
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
        have b3e67 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b3e68 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
        clear b3e67
        have b3e69 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e68
             have r₂ := b3e20
             grind)
          | exact resolve b3e68 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e72 : y = (M.op x x) := by
          first
          | (have i₁ := b3e69
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e69
          | exact resolve b3e69 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e69
        have b3e75 : False := by grind
        exact b3e75
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X3 X0) X2) := by
            intro X0 X1 X2 X3
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ x)) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (σ y) (σ x) X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 x X0 X1 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : y = (M.op x y) := by
            first
            | (have i₁ := b4e36 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e36
            | exact resolve b4e36 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e155 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e30 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e30
            | exact resolve b4e30 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30
          have b4e179 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e155
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e155
            | exact resolve b4e155 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e155
          have b4e273 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e179
               grind)
            | exact superpose b4e179 b4e20
            | exact resolve b4e20 b4e179
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e179
          have b4e283 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e273
               have i₂ := b4e45
               grind)
            | exact superpose b4e45 b4e273
            | exact resolve b4e273 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45 b4e273
          have b4e284 : False := by grind
          exact b4e284
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X3 X0) X2) := by
            intro X0 X1 X2 X3
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e19
            | exact resolve b5e19 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op y X1) := by
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
          have b5e35 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X1 X2 x
               have i₂ := b5e13 X0 X3 X2 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 : G, (M.op y (M.op X1 X0)) = (M.op x (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e32 x (M.op X1 X0)
               have i₂ := b5e32 X1 X0
               grind)
            | exact superpose b5e32 b5e32
            | exact resolve b5e32 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : y = (M.op x y) := by
            first
            | (have i₁ := b5e32 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e32
            | exact resolve b5e32 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e46 : ∀ X0 X1 : G, (M.op y X0) = (M.op y (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e41 X0 X1
               have i₂ := b5e32 y X0
               grind)
            | exact superpose b5e32 b5e41
            | exact resolve b5e41 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e52 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
          have b5e53 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
          clear b5e52
          have b5e54 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e53
               have r₂ := b5e21
               grind)
            | exact resolve b5e53 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e60 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b5e32 x y
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e32
            | exact resolve b5e32 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e62 : y = (M.op y y) := by
            first
            | (have i₁ := b5e60
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e60
            | exact resolve b5e60 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e71 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X0 X3) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X2 X3 X1
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2 X3
               have i₂ := b5e18 X0 (M.op X3 X0)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X1 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e73 : ∀ X0 X1 X2 X3 : G, (k (M.op X3 X1) X0) = (M.op (M.op X3 X1) X0) ∨ (M.op X1 (M.op X2 (M.op X3 X1))) = X0 ∨ (M.op X0 (M.op X3 X1)) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X2 (M.op X3 X1) X3
               have i₂ := b5e18 (M.op X3 X1) X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2 X3
               have i₂ := b5e18 X0 (M.op (M.op X3 X0) X2)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 (M.op X3 X1) X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e75 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ x) X0
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 (σ x) X0
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e76 : y = (k y y) := by grind
          have b5e245 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op y X0)) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e35 X1 X2 (M.op X3 X0) y
               have i₂ := b5e46 X0 X3
               grind)
            | exact superpose b5e46 b5e35
            | exact resolve b5e35 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e3042 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e75 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75
          have b5e3043 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e3042
               have r₂ := b5e24
               grind)
            | exact resolve b5e3042 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3042
          have b5e3044 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e3043
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e3043
            | exact resolve b5e3043 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3043
          have b5e3045 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e3044
               have i₂ := b5e54
               grind)
            | exact superpose b5e54 b5e3044
            | exact resolve b5e3044 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54 b5e3044
          have b5e3048 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (σ (M.op x x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (σ y) X0 X1 (σ x)
               have i₂ := b5e3045
               grind)
            | exact superpose b5e3045 b5e13
            | exact resolve b5e13 b5e3045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3062 : ∀ X0 X1 : G, (M.op X0 (σ (M.op x x))) = (M.op X0 (M.op X1 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b5e35 X0 X1 (σ y) (σ x)
               have i₂ := b5e3045
               grind)
            | exact superpose b5e3045 b5e35
            | exact resolve b5e35 b5e3045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3295 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e71 X0 X1 X2 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71
          have b5e4771 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e67 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67
          have b5e4772 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e4771 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4771
          have b5e5103 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = X1 ∨ (M.op y X1) = (k y X1) ∨ (M.op X1 y) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e73 X0 y x y
               have i₂ := b5e62
               grind)
            | exact superpose b5e62 b5e73
            | exact resolve b5e73 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e5320 : ∀ X1 : G, (M.op y X1) = (k y X1) ∨ (M.op X1 y) = X1 := by
            intro X1
            first
            | (have j0 := b5e5103 x X1
               have j1 := b5e3295 X1 y x
               grind)
            | (have r₁ := b5e5103 x x
               have r₂ := b5e3295 x y x
               grind)
            | (have r₁ := b5e5103 x (M.op X1 (M.op x X1))
               have r₂ := b5e3295 (M.op y (M.op x y)) X1 x
               grind)
            | (have r₁ := b5e5103 x (M.op x y)
               have r₂ := b5e3295 (k y (M.op x y)) y x
               grind)
            | exact resolve b5e5103 b5e3295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5103
          have b5e6443 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) ∨ (τ X0) = (M.op (τ X0) y) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 y
               have i₂ := b5e5320 (τ X0)
               grind)
            | exact superpose b5e5320 b5e27
            | (have j1 := b5e5320 (τ X0)
               grind)
            | exact resolve b5e27 b5e5320
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e5320
          have b5e13867 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ y) (M.op X0 (M.op X1 (σ y)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e3048 X0 (M.op X1 (σ y))
               have i₂ := b5e3062 (σ (M.op x x)) X1
               grind)
            | exact superpose b5e3062 b5e3048
            | exact resolve b5e3048 b5e3062
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3048 b5e3062
          have b5e14016 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ y) (M.op y (σ y))) := by
            first
            | (have i₁ := b5e13867 x x
               have i₂ := b5e245 (σ y) (σ y) x x
               grind)
            | exact superpose b5e245 b5e13867
            | exact resolve b5e13867 b5e245
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e245 b5e13867
          have b5e15353 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e4772 y
               have i₂ := b5e76
               grind)
            | exact superpose b5e76 b5e4772
            | (have j0 := b5e4772 y
               grind)
            | exact resolve b5e4772 b5e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76 b5e4772
          have b5e15358 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e15353
          have b5e15403 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b5e35 X0 X1 (σ y) (σ y)
               have i₂ := b5e15358
               grind)
            | exact superpose b5e15358 b5e35
            | exact resolve b5e35 b5e15358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e15415 : ∀ X0 X1 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op (σ y) (M.op X1 (σ y))) = X0 ∨ (M.op X0 (σ y)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e73 X0 (σ y) x (σ y)
               have i₂ := b5e15358
               grind)
            | exact superpose b5e15358 b5e73
            | exact resolve b5e73 b5e15358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e15445 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b5e15415 X0 x
               have j1 := b5e3295 X0 (σ y) x
               grind)
            | (have r₁ := b5e15415 (M.op x (σ y)) x
               have r₂ := b5e3295 (k (σ y) (M.op x (σ y))) (σ y) x
               grind)
            | (have r₁ := b5e15415 X0 x
               have r₂ := b5e3295 X0 (σ y) x
               grind)
            | (have r₁ := b5e15415 (M.op x (M.op x x)) x
               have r₂ := b5e3295 (M.op (σ y) (M.op x (σ y))) x x
               grind)
            | exact resolve b5e15415 b5e3295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3295 b5e15415
          have b5e84661 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e19 y X0
               have i₂ := b5e15445 (σ X0)
               grind)
            | exact superpose b5e15445 b5e19
            | (have j1 := b5e15445 (σ X0)
               grind)
            | exact resolve b5e19 b5e15445
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15445
          have b5e198018 : ∀ X0 : G, (σ (M.op y X0)) = (k (σ y) (σ X0)) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e6443 (σ X0)
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e6443
            | exact resolve b5e6443 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6443
          have b5e198075 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e198018 X0
               have i₂ := b5e19 y X0
               grind)
            | exact superpose b5e19 b5e198018
            | (have j0 := b5e198018 X0
               grind)
            | exact resolve b5e198018 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e198018
          have b5e312551 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e84661 x
               grind)
            | exact superpose b5e84661 b5e24
            | (have j1 := b5e84661 x
               grind)
            | exact resolve b5e24 b5e84661
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84661
          have b5e312946 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e312551
               have i₂ := b5e3045
               grind)
            | exact superpose b5e3045 b5e312551
            | exact resolve b5e312551 b5e3045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3045 b5e312551
          have b5e315456 : (σ y) ≠ (σ (M.op y x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e312946
               have i₂ := b5e198075 x
               grind)
            | exact superpose b5e198075 b5e312946
            | (have j1 := b5e198075 x
               grind)
            | exact resolve b5e312946 b5e198075
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e198075 b5e312946
          have b5e315457 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e315456
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e315456
            | exact resolve b5e315456 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e315456
          have b5e315458 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by grind
          clear b5e315457
          have b5e315469 : (σ x) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b5e315458
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e315458
            | exact resolve b5e315458 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e315458
          have b5e317913 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op y (σ y))) ∨ x = y := by
            first
            | (have i₁ := b5e14016
               have i₂ := b5e315469
               grind)
            | exact superpose b5e315469 b5e14016
            | exact resolve b5e14016 b5e315469
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14016 b5e315469
          have b5e318041 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b5e317913
               have i₂ := b5e15403 (σ y) y
               grind)
            | exact superpose b5e15403 b5e317913
            | exact resolve b5e317913 b5e15403
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15403 b5e317913
          have b5e318066 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e318041
               have i₂ := b5e15358
               grind)
            | exact superpose b5e15358 b5e318041
            | exact resolve b5e318041 b5e15358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e318041
          have b5e318072 : x = y := by
            first
            | (have r₁ := b5e318066
               have r₂ := b5e23
               grind)
            | exact resolve b5e318066 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e318066
          have b5e321152 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e318072
               grind)
            | exact superpose b5e318072 b5e24
            | exact resolve b5e24 b5e318072
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e321225 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e15358
               have i₂ := b5e318072
               grind)
            | exact superpose b5e318072 b5e15358
            | exact resolve b5e15358 b5e318072
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15358 b5e318072
          have b5e321337 : False := by grind
          exact b5e321337
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
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
        have b6e80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b6e83 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
        have b6e91 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e83
             have r₂ := b6e20
             grind)
          | exact resolve b6e83 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
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
        have b6e4374 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e80 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e80
          | exact resolve b6e80 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80
        have b6e4520 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e4374
        have b6e5424 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e4520
             grind)
          | exact superpose b6e4520 b6e13
          | exact resolve b6e13 b6e4520
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e5442 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e5424
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e5424
          | exact resolve b6e5424 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5424
        have b6e6026 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e5442
             grind)
          | exact superpose b6e5442 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e5442
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5442
        have b6e6027 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e6026
        have b6e6029 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e6027
             have r₂ := b6e20
             grind)
          | exact resolve b6e6027 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6027
        have b6e6345 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e6029
        have b6e7923 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e4520
             have i₂ := b6e6345
             grind)
          | exact superpose b6e6345 b6e4520
          | exact resolve b6e4520 b6e6345
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4520 b6e6345
        have b6e7930 : (σ x) = (σ y) := by grind
        clear b6e7923
        have b6e8711 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e7930
             grind)
          | exact superpose b6e7930 b6e19
          | exact resolve b6e19 b6e7930
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7930
        have b6e8734 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e8711
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e8711
          | exact resolve b6e8711 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8711
        have b6e8738 : False := by grind
        exact b6e8738
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X3 X0) X2) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ x)) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ y) (σ x) X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ x) X0 X1 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e38 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (k (M.op X1 X2) (M.op (M.op X0 (M.op X1 X2)) X2)) := by
            intro X0 X1 X2
            grind
          have b7e45 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e48 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e45
          have b7e49 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e48
               have r₂ := b7e23
               grind)
            | exact resolve b7e48 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e50 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e49
            | exact resolve b7e49 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b7e74 : (σ y) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e23
            | exact resolve b7e23 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e78 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ (k x y)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ x) X0 X1 (σ x)
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e13
            | exact resolve b7e13 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e79 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ x)) = (M.op X0 (σ (k x y))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ x) (σ x) X1
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e13
            | exact resolve b7e13 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e80 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b7e79 X0 x
               have i₂ := b7e28 X0 x
               grind)
            | exact superpose b7e28 b7e79
            | exact resolve b7e79 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79
          have b7e81 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ (k x y)) X1) := by
            intro X1
            first
            | (have i₁ := b7e78 x X1
               have i₂ := b7e33 x X1
               grind)
            | exact superpose b7e33 b7e78
            | exact resolve b7e78 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e78
          have b7e83 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e28 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e28
            | exact resolve b7e28 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e87 : ∀ X0 X1 X2 : G, (M.op X2 (σ y)) = (M.op (M.op X0 (M.op X1 X2)) (σ x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e28 X2 (M.op x X0)
               have i₂ := b7e13 X0 X1 X2 x
               grind)
            | exact superpose b7e13 b7e28
            | exact resolve b7e28 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e88 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e28 (σ x) (M.op x X0)
               have i₂ := b7e28 X0 x
               grind)
            | exact superpose b7e28 b7e28
            | exact resolve b7e28 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e97 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e88 x
               have i₂ := b7e28 (σ y) x
               grind)
            | exact superpose b7e28 b7e88
            | exact resolve b7e88 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e98 : ∀ X1 X2 : G, (M.op X2 (σ y)) = (M.op (M.op X1 X2) (σ y)) := by
            intro X1 X2
            first
            | (have i₁ := b7e87 x X1 X2
               have i₂ := b7e28 (M.op X1 X2) x
               grind)
            | exact superpose b7e28 b7e87
            | exact resolve b7e87 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e101 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e83
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e83
            | exact resolve b7e83 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e873 : (M.op (σ (k x y)) (σ y)) = (k (σ (k x y)) (M.op (σ (k x y)) (σ y))) := by grind
          clear b7e80
          have b7e917 : (M.op (σ y) (σ y)) = (k (σ (k x y)) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b7e873
               have i₂ := b7e81 (σ y)
               grind)
            | exact superpose b7e81 b7e873
            | exact resolve b7e873 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81 b7e873
          have b7e930 : (M.op (σ x) (σ y)) = (k (σ (k x y)) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b7e917
               have i₂ := b7e97
               grind)
            | exact superpose b7e97 b7e917
            | exact resolve b7e917 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97 b7e917
          have b7e941 : (σ y) = (k (σ (k x y)) (σ y)) := by
            first
            | (have i₁ := b7e930
               have i₂ := b7e101
               grind)
            | exact superpose b7e101 b7e930
            | exact resolve b7e930 b7e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e930
          have b7e945 : (σ y) = (σ (k (k x y) y)) := by
            first
            | (have i₁ := b7e941
               have i₂ := b7e19 (k x y) y
               grind)
            | exact superpose b7e19 b7e941
            | exact resolve b7e941 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e941
          have b7e1256 : (σ y) = (σ (k (M.op x y) y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e945
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e945
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e945 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1267 : (σ y) = (σ (k (M.op x y) y)) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e1256
               have r₂ := b7e21
               grind)
            | exact resolve b7e1256 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1256
          have b7e1268 : (σ y) = (σ (k (M.op x y) y)) := by
            first
            | (have r₁ := b7e1267
               have r₂ := b7e22
               grind)
            | exact resolve b7e1267 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1267
          have b7e1676 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = (k (M.op X0 (σ x)) (M.op (M.op X0 (σ x)) (σ y))) := by
            intro X0
            first
            | (have i₁ := b7e38 x x (σ x)
               have i₂ := b7e28 (M.op x (σ x)) x
               grind)
            | exact superpose b7e28 b7e38
            | exact resolve b7e38 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28 b7e38
          have b7e1697 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
            intro X0
            first
            | (have i₁ := b7e1676 X0
               have i₂ := b7e98 x (M.op X0 (σ x))
               grind)
            | (have i₁ := b7e1676 x
               have i₂ := b7e98 x (σ x)
               grind)
            | exact superpose b7e98 b7e1676
            | exact resolve b7e1676 b7e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98 b7e1676
          have b7e1720 : ∀ X0 : G, (σ y) = (k (M.op X0 (σ x)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e1697 X0
               have i₂ := b7e101
               grind)
            | exact superpose b7e101 b7e1697
            | exact resolve b7e1697 b7e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101 b7e1697
          have b7e1854 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e1720 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e1720
            | exact resolve b7e1720 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1720
          have b7e1874 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e1854
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e1854
            | exact resolve b7e1854 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1854
          have b7e1884 : (τ (σ y)) = (k y y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e1874
               grind)
            | exact superpose b7e1874 b7e14
            | exact resolve b7e14 b7e1874
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1874
          have b7e1886 : y = (k y y) := by
            first
            | (have i₁ := b7e1884
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e1884
            | exact resolve b7e1884 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1884
          have b7e2125 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e1886
               grind)
            | exact superpose b7e1886 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e1886
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1886
          have b7e2126 : y = (M.op y y) := by grind
          clear b7e2125
          have b7e2375 : ∀ X0 X1 : G, (M.op y X1) = (M.op y (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 y X0 X1 y
               have i₂ := b7e2126
               grind)
            | exact superpose b7e2126 b7e13
            | exact resolve b7e13 b7e2126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2627 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e64 x x
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e64
            | exact resolve b7e64 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50 b7e64
          have b7e2757 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by grind
          clear b7e2627
          have b7e19920 : (k x y) = (τ (σ (k x x))) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e2757
               grind)
            | exact superpose b7e2757 b7e14
            | exact resolve b7e14 b7e2757
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2757
          have b7e19951 : (σ x) = (σ (k x y)) ∨ (k x y) = (k x x) := by
            first
            | (have i₁ := b7e19920
               have i₂ := b7e14 (k x x)
               grind)
            | exact superpose b7e14 b7e19920
            | exact resolve b7e19920 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e19920
          have b7e21658 : (k x y) = (τ (σ x)) ∨ (k x y) = (k x x) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e19951
               grind)
            | exact superpose b7e19951 b7e14
            | exact resolve b7e14 b7e19951
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e19951
          have b7e21691 : (k x y) = (k x x) ∨ x = (k x y) := by
            first
            | (have i₁ := b7e21658
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e21658
            | exact resolve b7e21658 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21658
          have b7e24685 : (M.op x y) = (k x x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ x = (k x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e21691
               grind)
            | exact superpose b7e21691 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e21691
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21691
          have b7e24687 : (M.op x y) = (k x x) ∨ y = (M.op y x) ∨ x = (k x y) := by
            first
            | (have r₁ := b7e24685
               have r₂ := b7e21
               grind)
            | exact resolve b7e24685 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e24685
          have b7e24695 : x = (k x y) ∨ (M.op x y) = (k x x) := by
            first
            | (have r₁ := b7e24687
               have r₂ := b7e22
               grind)
            | exact resolve b7e24687 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e24687
          have b7e30094 : (σ y) = (σ (k x y)) ∨ (M.op x y) = (k x x) := by
            first
            | (have i₁ := b7e945
               have i₂ := b7e24695
               grind)
            | exact superpose b7e24695 b7e945
            | exact resolve b7e945 b7e24695
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e945 b7e24695
          have b7e30101 : (M.op x y) = (k x x) := by
            first
            | (have r₁ := b7e30094
               have r₂ := b7e74
               grind)
            | exact resolve b7e30094 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30094
          have b7e32171 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x x
               have i₂ := b7e30101
               grind)
            | exact superpose b7e30101 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e30101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32172 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
          clear b7e32171
          have b7e39476 : (M.op y y) = (M.op y (M.op x x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e2375 x y
               have i₂ := b7e32172
               grind)
            | exact superpose b7e32172 b7e2375
            | exact resolve b7e2375 b7e32172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32172
          have b7e39482 : (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e39476
               have i₂ := b7e2375 x x
               grind)
            | exact superpose b7e2375 b7e39476
            | exact resolve b7e39476 b7e2375
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2375 b7e39476
          have b7e39560 : y = (M.op y x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e39482
               have i₂ := b7e2126
               grind)
            | exact superpose b7e2126 b7e39482
            | exact resolve b7e39482 b7e2126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2126 b7e39482
          have b7e39616 : x = (M.op x x) := by
            first
            | (have r₁ := b7e39560
               have r₂ := b7e22
               grind)
            | exact resolve b7e39560 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39560
          have b7e39935 : x = (k x x) := by grind
          clear b7e39616
          have b7e40221 : x = (M.op x y) := by
            first
            | (have i₁ := b7e30101
               have i₂ := b7e39935
               grind)
            | exact superpose b7e39935 b7e30101
            | exact resolve b7e30101 b7e39935
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30101 b7e39935
          have b7e40293 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e1268
               have i₂ := b7e40221
               grind)
            | exact superpose b7e40221 b7e1268
            | exact resolve b7e1268 b7e40221
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1268 b7e40221
          have b7e40468 : False := by grind
          exact b7e40468
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e66 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1863 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e66 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e1864 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1863
               have r₂ := b8e24
               grind)
            | exact resolve b8e1863 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1863
          have b8e1865 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1864
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1864
            | exact resolve b8e1864 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1864
          have b8e1866 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1865
               grind)
            | exact superpose b8e1865 b8e20
            | exact resolve b8e20 b8e1865
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1865
          have b8e2135 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e1866
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1866
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1866 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1866
          have b8e2136 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e2135
          have b8e2138 : y = (M.op y x) := by
            first
            | (have r₁ := b8e2136
               have r₂ := b8e21
               grind)
            | exact resolve b8e2136 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2136
          have b8e2140 : False := by grind
          exact b8e2140
