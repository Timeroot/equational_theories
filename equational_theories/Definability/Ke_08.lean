import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3479`: `x ◇ x = y ◇ ((x ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyy_pxy_pxx_pyx_Equation3479 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3479 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3479.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op y x) = (M.op y y) := by grind
      have b0e20 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e73 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (k x y) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 y y
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e80 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ y) (σ y)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e88 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e80
      have b0e93 : (M.op x y) = (k x y) := by grind
      clear b0e73
      have b0e94 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e88
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e88
        | exact resolve b0e88 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e88
      have b0e97 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e94
           have i₂ := b0e93
           grind)
        | exact superpose b0e93 b0e94
        | exact resolve b0e94 b0e93
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e93 b0e94
      have b0e98 : False := by grind
      exact b0e98
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X2) X2)) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op y x) = (M.op y y) := by grind
        have b1e21 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X1 X2 (M.op (M.op X0 x) x)
             have i₂ := b1e12 X0 (M.op X1 (M.op (M.op X0 x) x)) x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e31 x X0 x
             have i₂ := b1e31 x X1 x
             grind)
          | (have i₁ := b1e31 X0 X1 (M.op X0 X0)
             have i₂ := b1e31 X0 (M.op X0 X0) x
             grind)
          | exact superpose b1e31 b1e31
          | exact resolve b1e31 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e77 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b1e23
             have i₂ := b1e42 (σ y) X0
             grind)
          | (have i₁ := b1e23
             have i₂ := b1e42 X0 (σ y)
             grind)
          | exact superpose b1e42 b1e23
          | exact resolve b1e23 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e42
        have b1e85 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (k x y) := by
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
        have b1e103 : (M.op x y) = (k x y) := by grind
        clear b1e85
        have b1e118 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b1e120 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e118
        have b1e121 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e120
             have r₂ := b1e21
             grind)
          | exact resolve b1e120 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e120
        have b1e126 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e121
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e121
          | exact resolve b1e121 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e121
        have b1e128 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e126
             have i₂ := b1e103
             grind)
          | exact superpose b1e103 b1e126
          | exact resolve b1e126 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e103 b1e126
        have b1e129 : False := by grind
        exact b1e129
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X2) X2)) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op y x) = (M.op y y) := by grind
        have b2e21 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e30 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 X2 (M.op (M.op X0 x) x)
             have i₂ := b2e12 X0 (M.op X1 (M.op (M.op X0 x) x)) x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e30 x X0 x
             have i₂ := b2e30 x X1 x
             grind)
          | (have i₁ := b2e30 X0 X1 (M.op X0 X0)
             have i₂ := b2e30 X0 (M.op X0 X0) x
             grind)
          | exact superpose b2e30 b2e30
          | exact resolve b2e30 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e78 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (k x y) := by
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
        have b2e80 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X0
             have i₂ := b2e41 X0 X1
             grind)
          | (have i₁ := b2e15 X1 X1
             have i₂ := b2e41 X0 X1
             grind)
          | exact superpose b2e41 b2e15
          | (have j0 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e41 X1 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e41 X0 X0
             grind)
          | exact resolve b2e15 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e86 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X2) ∨ (k X2 X1) = (M.op X2 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X2 X1
             have i₂ := b2e41 X1 X0
             grind)
          | (have i₁ := b2e15 X2 X1
             have i₂ := b2e41 X0 X1
             grind)
          | exact superpose b2e41 b2e15
          | (have j0 := b2e15 X2 X1
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e41 X1 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e41 X0 X0
             grind)
          | exact resolve b2e15 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e87 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) ≠ (M.op X0 (M.op X1 X1)) ∨ (k X3 X2) = (M.op X3 X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e15 X3 X2
             have i₂ := b2e30 X1 X2 X0
             grind)
          | (have i₁ := b2e15 X0 (M.op X0 X0)
             have i₂ := b2e30 X0 X1 (M.op X0 X0)
             grind)
          | exact superpose b2e30 b2e15
          | (have j0 := b2e15 X3 X2
             grind)
          | (have r₁ := b2e15 (M.op X0 X0) (M.op X0 X0)
             have r₂ := b2e30 X0 (M.op X0 X0) (M.op X0 X0)
             grind)
          | (have r₁ := b2e15 (M.op X0 X0) X1
             have r₂ := b2e30 X0 X1 X1
             grind)
          | exact resolve b2e15 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e91 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e94 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e80 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e80
        have b2e96 : (M.op x y) = (k x y) := by grind
        clear b2e78
        have b2e100 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e91 (σ X0)
             grind)
          | exact superpose b2e91 b2e18
          | exact resolve b2e18 b2e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e103 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e100 X0
             have i₂ := b2e91 X0
             grind)
          | exact superpose b2e91 b2e100
          | exact resolve b2e100 b2e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e100
        have b2e153 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X3 X3)) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e30 X3 X0 X2
             have i₂ := b2e17 X1 X0
             grind)
          | (have i₁ := b2e30 X0 X0 X2
             have i₂ := b2e17 X0 X0
             grind)
          | exact superpose b2e17 b2e30
          | (have j1 := b2e17 X1 X0
             grind)
          | exact resolve b2e30 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e171 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X1 X0
             have i₂ := b2e17 X1 X0
             grind)
          | (have i₁ := b2e16 X1 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e16
          | (have j0 := b2e16 X1 X0
             have j1 := b2e17 X1 X0
             grind)
          | (have r₁ := b2e16 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | (have r₁ := b2e16 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e16 X1 X1
             have r₂ := b2e17 X1 X1
             grind)
          | exact resolve b2e16 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e172 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e17 X1 X0
             grind)
          | (have i₁ := b2e15 X1 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X1
             have j1 := b2e17 X1 X0
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e17 X1 X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e176 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
        have b2e181 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e171 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e171
        have b2e182 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e181 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e181
        have b2e186 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e176 X0 X1
             have i₂ := b2e103 X0
             grind)
          | exact superpose b2e103 b2e176
          | (have j0 := b2e176 X0 X1
             grind)
          | exact resolve b2e176 b2e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e176
        have b2e187 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e172 X0 X1
             grind)
          | (have r₁ := b2e172 X0 X1
             have r₂ := b2e41 X0 X1
             grind)
          | (have r₁ := b2e172 X1 X0
             have r₂ := b2e41 X0 X1
             grind)
          | exact resolve b2e172 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e172
        have b2e192 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e186 X0 X1
             have i₂ := b2e103 X0
             grind)
          | exact superpose b2e103 b2e186
          | (have j0 := b2e186 X0 X1
             grind)
          | exact resolve b2e186 b2e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e186
        have b2e220 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X1
             have i₂ := b2e94 X0 (σ X1)
             grind)
          | exact superpose b2e94 b2e18
          | exact resolve b2e18 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e94
        have b2e224 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e220 X0 X1
             have i₂ := b2e91 X1
             grind)
          | exact superpose b2e91 b2e220
          | exact resolve b2e220 b2e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91 b2e220
        have b2e462 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (σ (M.op X0 X0)) ∨ (k X2 X1) = (M.op X2 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X2 X1
             have i₂ := b2e224 X1 X0
             grind)
          | exact superpose b2e224 b2e15
          | (have j0 := b2e15 X2 X1
             grind)
          | exact resolve b2e15 b2e224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1789 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e182 X0 X1
             grind)
          | (have i₁ := b2e15 X0 X0
             have i₂ := b2e182 X0 X1
             grind)
          | exact superpose b2e182 b2e15
          | (have j0 := b2e15 X0 X0
             have j1 := b2e182 X0 X1
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e182 X1 X1
             grind)
          | (have r₁ := b2e15 X1 X0
             have r₂ := b2e182 X0 X1
             grind)
          | exact resolve b2e15 b2e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e182
        have b2e1876 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e1789 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1789
        have b2e2402 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X0 X1
             have i₂ := b2e187 X0 X1
             grind)
          | (have i₁ := b2e16 X0 X0
             have i₂ := b2e187 X0 X1
             grind)
          | exact superpose b2e187 b2e16
          | (have j0 := b2e16 X0 X1
             have j1 := b2e187 X0 X1
             grind)
          | (have r₁ := b2e16 X1 X1
             have r₂ := b2e187 X1 X1
             grind)
          | exact resolve b2e16 b2e187
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e187
        have b2e2447 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e2402 X0 X1
             have j1 := b2e86 X0 X1 X1
             grind)
          | (have r₁ := b2e2402 x x
             have r₂ := b2e86 x x x
             grind)
          | (have r₁ := b2e2402 x X0
             have r₂ := b2e86 X0 X0 x
             grind)
          | exact resolve b2e2402 b2e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e86 b2e2402
        have b2e2464 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e2447 X0 X1
             grind)
          | (have r₁ := b2e2447 X0 X1
             have r₂ := b2e41 X0 X1
             grind)
          | (have r₁ := b2e2447 X1 X0
             have r₂ := b2e41 X0 X1
             grind)
          | exact resolve b2e2447 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41 b2e2447
        have b2e8892 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e192 y x
             grind)
          | exact superpose b2e192 b2e22
          | (have j1 := b2e192 y x
             grind)
          | exact resolve b2e22 b2e192
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e192
        have b2e9293 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have r₁ := b2e8892
             have r₂ := b2e224 (σ y) y
             grind)
          | exact resolve b2e8892 b2e224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8892
        have b2e9379 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e9293
             have i₂ := b2e96
             grind)
          | exact superpose b2e96 b2e9293
          | exact resolve b2e9293 b2e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9293
        have b2e49995 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
          intro X0 X1
          first
          | (have i₁ := b2e87 X0 X1 (σ y) (σ x)
             have i₂ := b2e9379
             grind)
          | exact superpose b2e9379 b2e87
          | (have j0 := b2e87 X0 X1 (σ y) (σ x)
             grind)
          | exact resolve b2e87 b2e9379
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87 b2e9379
        have b2e50057 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          intro X0 X1
          first
          | (have j0 := b2e49995 X0 X1
             have j1 := b2e462 X0 (σ y) (σ x)
             grind)
          | (have r₁ := b2e49995 X0 X1
             have r₂ := b2e462 y (σ y) (σ x)
             grind)
          | exact resolve b2e49995 b2e462
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e462 b2e49995
        have b2e50078 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e50057 X0 X1
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e50057
          | (have j0 := b2e50057 X0 X1
             grind)
          | exact resolve b2e50057 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50057
        have b2e50088 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e50078 X0 X1
             have i₂ := b2e96
             grind)
          | exact superpose b2e96 b2e50078
          | (have j0 := b2e50078 X0 X1
             grind)
          | exact resolve b2e50078 b2e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50078
        have b2e50096 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e50088 X0 X1
             grind)
          | (have r₁ := b2e50088 X0 X1
             have r₂ := b2e19
             grind)
          | exact resolve b2e50088 b2e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50088
        have b2e50434 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e50096 (M.op x x) x
             have i₂ := b2e224 (M.op x x) X0
             grind)
          | exact superpose b2e224 b2e50096
          | exact resolve b2e50096 b2e224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50096
        have b2e51414 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e1876 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1876
        have b2e53239 : (M.op x y) = (M.op y x) ∨ (M.op y y) = (k y x) ∨ (M.op y x) = (k y x) := by
          first
          | (have i₁ := b2e96
             have i₂ := b2e2464 y x
             grind)
          | exact superpose b2e2464 b2e96
          | (have j1 := b2e2464 y x
             grind)
          | exact resolve b2e96 b2e2464
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2464
        have b2e53352 : (M.op y y) = (k y x) ∨ (M.op y x) = (k y x) := by
          first
          | (have j1 := b2e51414 y x
             grind)
          | (have r₁ := b2e53239
             have r₂ := b2e51414 y x
             grind)
          | (have r₁ := b2e53239
             have r₂ := b2e51414 x y
             grind)
          | exact resolve b2e53239 b2e51414
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51414 b2e53239
        have b2e53476 : (M.op y y) = (k y x) ∨ (M.op y y) = (k y x) := by
          first
          | (have i₁ := b2e53352
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e53352
          | exact resolve b2e53352 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53352
        have b2e53477 : (M.op y y) = (k y x) := by grind
        clear b2e53476
        have b2e64096 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e22
             have i₂ := b2e153 (σ x) (σ y) X0 X1
             grind)
          | exact superpose b2e153 b2e22
          | (have j1 := b2e153 (σ x) (σ y) x x
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e153 (σ y) (σ x) x x
             grind)
          | exact resolve b2e22 b2e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e64099 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b2e21
             have i₂ := b2e153 (σ y) (σ x) X0 X1
             grind)
          | exact superpose b2e153 b2e21
          | (have j1 := b2e153 (σ y) (σ x) x x
             grind)
          | exact resolve b2e21 b2e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e153
        have b2e65163 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          intro X0 X1
          first
          | (have j0 := b2e64099 X0 X1
             grind)
          | (have r₁ := b2e64099 X0 X1
             have r₂ := b2e22
             grind)
          | exact resolve b2e64099 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64099
        have b2e65164 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b2e64096 x x
             have r₂ := b2e30 x (σ y) x
             grind)
          | exact resolve b2e64096 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64096
        have b2e65235 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e65163 x x
             have r₂ := b2e30 x (σ y) x
             grind)
          | exact resolve b2e65163 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30 b2e65163
        have b2e65236 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b2e65164
             have i₂ := b2e103 x
             grind)
          | exact superpose b2e103 b2e65164
          | exact resolve b2e65164 b2e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e103 b2e65164
        have b2e65241 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e65235
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e65235
          | exact resolve b2e65235 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65235
        have b2e65242 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e65236
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e65236
          | exact resolve b2e65236 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65236
        have b2e65244 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e65241
             have i₂ := b2e96
             grind)
          | exact superpose b2e96 b2e65241
          | exact resolve b2e65241 b2e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e96 b2e65241
        have b2e65245 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e65242
             have i₂ := b2e53477
             grind)
          | exact superpose b2e53477 b2e65242
          | exact resolve b2e65242 b2e53477
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53477 b2e65242
        have b2e65246 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e65245
             have i₂ := b2e65244
             grind)
          | exact superpose b2e65244 b2e65245
          | exact resolve b2e65245 b2e65244
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65244 b2e65245
        have b2e65247 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have r₁ := b2e65246
             have r₂ := b2e50434 x
             grind)
          | exact resolve b2e65246 b2e50434
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50434 b2e65246
        have b2e67375 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e65247
             grind)
          | exact superpose b2e65247 b2e22
          | exact resolve b2e22 b2e65247
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65247
        have b2e67473 : False := by grind
        exact b2e67473
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X2) X2)) := by
          intro X0 X1 X2
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op y x) ≠ (M.op y y) := by grind
        have b3e21 : (M.op x y) = (M.op y y) := by grind
        have b3e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op (M.op y y) y)) := by
          intro X0
          first
          | (have i₁ := b3e12 x X0 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : (M.op y y) = (M.op x x) := by
          first
          | (have i₁ := b3e32 x
             have i₂ := b3e12 y x y
             grind)
          | (have i₁ := b3e32 (M.op (M.op y y) y)
             have i₂ := b3e12 (M.op (M.op y y) y) x x
             grind)
          | exact superpose b3e12 b3e32
          | exact resolve b3e32 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e64 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e71 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e64
        have b3e75 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e71
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e71
          | exact resolve b3e71 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e71
        have b3e91 : (M.op y y) ≠ (M.op y y) ∨ (M.op y x) = (M.op y y) ∨ (M.op x x) = (k x y) := by
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
        have b3e95 : (M.op y x) = (M.op y y) ∨ (M.op x x) = (k x y) := by grind
        clear b3e91
        have b3e98 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e95
             have r₂ := b3e20
             grind)
          | exact resolve b3e95 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e95
        have b3e102 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b3e98
             have i₂ := b3e38
             grind)
          | exact superpose b3e38 b3e98
          | exact resolve b3e98 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38 b3e98
        have b3e273 : (σ (M.op y y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e75
             grind)
          | exact superpose b3e75 b3e23
          | exact resolve b3e23 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e75
        have b3e277 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e273
             have i₂ := b3e102
             grind)
          | exact superpose b3e102 b3e273
          | exact resolve b3e273 b3e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e102 b3e273
        have b3e278 : False := by grind
        exact b3e278
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X2) X2)) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op y y) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e25
            | exact resolve b4e25 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e38 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X2 (M.op (M.op X0 x) x)
               have i₂ := b4e13 X0 (M.op X1 (M.op (M.op X0 x) x)) x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e52 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e38 x X0 x
               have i₂ := b4e38 x X1 x
               grind)
            | (have i₁ := b4e38 X0 X1 (M.op X0 X0)
               have i₂ := b4e38 X0 (M.op X0 X0) x
               grind)
            | exact superpose b4e38 b4e38
            | exact resolve b4e38 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e92 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b4e26
               have i₂ := b4e52 (σ y) X0
               grind)
            | (have i₁ := b4e26
               have i₂ := b4e52 X0 (σ y)
               grind)
            | exact superpose b4e52 b4e26
            | exact resolve b4e26 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e96 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X0 X0
               have i₂ := b4e52 X0 X1
               grind)
            | (have i₁ := b4e16 X1 X1
               have i₂ := b4e52 X0 X1
               grind)
            | exact superpose b4e52 b4e16
            | (have j0 := b4e16 X0 X0
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e52 X1 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e52 X0 X0
               grind)
            | exact resolve b4e16 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e108 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e111 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e96 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96
          have b4e255 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X1
               have i₂ := b4e111 X0 (σ X1)
               grind)
            | exact superpose b4e111 b4e19
            | exact resolve b4e19 b4e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e111
          have b4e259 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e255 X0 X1
               have i₂ := b4e108 X1
               grind)
            | exact superpose b4e108 b4e255
            | exact resolve b4e255 b4e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e108 b4e255
          have b4e406 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e92 X1
               have i₂ := b4e52 y X0
               grind)
            | (have i₁ := b4e92 X1
               have i₂ := b4e52 X0 y
               grind)
            | exact superpose b4e52 b4e92
            | exact resolve b4e92 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52 b4e92
          have b4e407 : False := by grind
          exact b4e407
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X2) X2)) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b5e22 : (M.op x y) = (M.op y y) := by grind
          have b5e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e20
            | exact resolve b5e20 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op (M.op y y) y)) := by
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
          have b5e37 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 (M.op (M.op X0 x) x)
               have i₂ := b5e13 X0 (M.op X1 (M.op (M.op X0 x) x)) x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : (M.op y y) = (M.op x x) := by
            first
            | (have i₁ := b5e34 x
               have i₂ := b5e13 y x y
               grind)
            | (have i₁ := b5e34 (M.op (M.op y y) y)
               have i₂ := b5e13 (M.op (M.op y y) y) x x
               grind)
            | exact superpose b5e13 b5e34
            | exact resolve b5e34 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e51 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e37 x X0 x
               have i₂ := b5e37 x X1 x
               grind)
            | (have i₁ := b5e37 X0 X1 (M.op X0 X0)
               have i₂ := b5e37 X0 (M.op X0 X0) x
               grind)
            | exact superpose b5e37 b5e37
            | exact resolve b5e37 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e90 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X0 X0
               have i₂ := b5e51 X0 X1
               grind)
            | (have i₁ := b5e16 X1 X1
               have i₂ := b5e51 X0 X1
               grind)
            | exact superpose b5e51 b5e16
            | (have j0 := b5e16 X0 X0
               grind)
            | (have r₁ := b5e16 X1 X1
               have r₂ := b5e51 X1 X1
               grind)
            | (have r₁ := b5e16 X0 X0
               have r₂ := b5e51 X0 X0
               grind)
            | exact resolve b5e16 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e102 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e105 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e90 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90
          have b5e111 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e102 (σ X0)
               grind)
            | exact superpose b5e102 b5e19
            | exact resolve b5e19 b5e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e111 X0
               have i₂ := b5e102 X0
               grind)
            | exact superpose b5e102 b5e111
            | exact resolve b5e111 b5e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e111
          have b5e124 : (M.op y y) ≠ (M.op y y) ∨ (M.op y x) = (M.op y y) ∨ (M.op x x) = (k x y) := by
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
          have b5e128 : (M.op y x) = (M.op y y) ∨ (M.op x x) = (k x y) := by grind
          clear b5e124
          have b5e131 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e128
               have r₂ := b5e21
               grind)
            | exact resolve b5e128 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e128
          have b5e135 : (M.op y y) = (k x y) := by
            first
            | (have i₁ := b5e131
               have i₂ := b5e40
               grind)
            | exact superpose b5e40 b5e131
            | exact resolve b5e131 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40 b5e131
          have b5e192 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
          have b5e204 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e192 X0 X1
               have i₂ := b5e114 X0
               grind)
            | exact superpose b5e114 b5e192
            | (have j0 := b5e192 X0 X1
               grind)
            | exact resolve b5e192 b5e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e192
          have b5e210 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e204 X0 X1
               have i₂ := b5e114 X0
               grind)
            | exact superpose b5e114 b5e204
            | (have j0 := b5e204 X0 X1
               grind)
            | exact resolve b5e204 b5e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e114 b5e204
          have b5e238 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X1
               have i₂ := b5e105 X0 (σ X1)
               grind)
            | exact superpose b5e105 b5e19
            | exact resolve b5e19 b5e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e105
          have b5e242 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e238 X0 X1
               have i₂ := b5e102 X1
               grind)
            | exact superpose b5e102 b5e238
            | exact resolve b5e238 b5e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e102 b5e238
          have b5e8174 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e25
               have i₂ := b5e210 y x
               grind)
            | exact superpose b5e210 b5e25
            | (have j1 := b5e210 y x
               grind)
            | (have r₁ := b5e25
               have r₂ := b5e210 y x
               grind)
            | exact resolve b5e25 b5e210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e210
          have b5e8428 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
          clear b5e8174
          have b5e8561 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e8428
               have i₂ := b5e135
               grind)
            | exact superpose b5e135 b5e8428
            | exact resolve b5e8428 b5e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e135 b5e8428
          have b5e8562 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by grind
          clear b5e8561
          have b5e8726 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e8562
               grind)
            | exact superpose b5e8562 b5e23
            | exact resolve b5e23 b5e8562
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8562
          have b5e8766 : False := by grind
          exact b5e8766
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X2) X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op y x) ≠ (M.op y y) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b6e33 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X1 X2 (M.op (M.op X0 x) x)
             have i₂ := b6e12 X0 (M.op X1 (M.op (M.op X0 x) x)) x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e44 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e33 x X0 x
             have i₂ := b6e33 x X1 x
             grind)
          | (have i₁ := b6e33 X0 X1 (M.op X0 X0)
             have i₂ := b6e33 X0 (M.op X0 X0) x
             grind)
          | exact superpose b6e33 b6e33
          | exact resolve b6e33 b6e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e79 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X0 X0
             have i₂ := b6e44 X0 X1
             grind)
          | (have i₁ := b6e15 X1 X1
             have i₂ := b6e44 X0 X1
             grind)
          | exact superpose b6e44 b6e15
          | (have j0 := b6e15 X0 X0
             grind)
          | (have r₁ := b6e15 X1 X1
             have r₂ := b6e44 X1 X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e44 X0 X0
             grind)
          | exact resolve b6e15 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e84 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e87 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) ≠ (M.op X0 (M.op X1 X1)) ∨ (k X3 X2) = (M.op X3 X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e15 X3 X2
             have i₂ := b6e33 X1 X2 X0
             grind)
          | (have i₁ := b6e15 X0 (M.op X0 X0)
             have i₂ := b6e33 X0 X1 (M.op X0 X0)
             grind)
          | exact superpose b6e33 b6e15
          | (have j0 := b6e15 X3 X2
             grind)
          | (have r₁ := b6e15 (M.op X0 X0) (M.op X0 X0)
             have r₂ := b6e33 X0 (M.op X0 X0) (M.op X0 X0)
             grind)
          | (have r₁ := b6e15 (M.op X0 X0) X1
             have r₂ := b6e33 X0 X1 X1
             grind)
          | exact resolve b6e15 b6e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e91 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e92 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e84
        have b6e95 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e79 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e97 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e92
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e92
          | exact resolve b6e92 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e92
        have b6e101 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e91 (σ X0)
             grind)
          | exact superpose b6e91 b6e18
          | exact resolve b6e18 b6e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e104 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e101 X0
             have i₂ := b6e91 X0
             grind)
          | exact superpose b6e91 b6e101
          | exact resolve b6e101 b6e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e91 b6e101
        have b6e109 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X3 X2) ∨ (M.op X2 X3) = (M.op X0 (M.op X1 X1)) ∨ (M.op X3 X3) = (k X3 X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e16 X0 X1
             have i₂ := b6e33 X0 X1 X2
             grind)
          | (have i₁ := b6e16 X0 (M.op X0 X0)
             have i₂ := b6e33 X0 X1 (M.op X0 X0)
             grind)
          | exact superpose b6e33 b6e16
          | (have j0 := b6e16 X3 X2
             grind)
          | (have r₁ := b6e16 X2 (M.op X0 X0)
             have r₂ := b6e33 X0 (M.op X0 X0) X2
             grind)
          | (have r₁ := b6e16 (M.op X0 X0) (M.op X0 X0)
             have r₂ := b6e33 X0 (M.op X0 X0) (M.op X0 X0)
             grind)
          | exact resolve b6e16 b6e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e143 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e23 X1 (τ X1)
             have i₂ := b6e95 X0 (τ X1)
             grind)
          | exact superpose b6e95 b6e23
          | exact resolve b6e23 b6e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e95
        have b6e146 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e143 X0 X1
             have i₂ := b6e14 X1
             grind)
          | exact superpose b6e14 b6e143
          | exact resolve b6e143 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e143
        have b6e180 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e17 X1 X0
             grind)
          | (have i₁ := b6e15 X1 X1
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X0 X0
             have j1 := b6e17 X1 X0
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 X0
             grind)
          | (have r₁ := b6e15 X1 X1
             have r₂ := b6e17 X1 X1
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e208 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X1 X0
             have i₂ := b6e17 X1 X0
             grind)
          | (have i₁ := b6e16 X1 X1
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e16
          | (have j0 := b6e16 X1 X0
             have j1 := b6e17 X1 X0
             grind)
          | (have r₁ := b6e16 X0 X0
             have r₂ := b6e17 X0 X0
             grind)
          | (have r₁ := b6e16 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e16 X1 X1
             have r₂ := b6e17 X1 X1
             grind)
          | exact resolve b6e16 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e217 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e208 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e208
        have b6e218 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e217 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e217
        have b6e221 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e180 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e180
        have b6e282 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
          intro X0 X2
          first
          | (have i₁ := b6e146 X2 x
             have i₂ := b6e146 X0 x
             grind)
          | exact superpose b6e146 b6e146
          | exact resolve b6e146 b6e146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e146
        have b6e319 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e97
             grind)
          | exact superpose b6e97 b6e19
          | exact resolve b6e19 b6e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1202 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e282 X2 X1
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e282 X0 X1
             have i₂ := b6e17 X1 X1
             grind)
          | exact superpose b6e17 b6e282
          | (have j1 := b6e17 X0 X1
             grind)
          | exact resolve b6e282 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e282
        have b6e1917 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (k x y) := by
          first
          | (have i₁ := b6e319
             have i₂ := b6e218 y x
             grind)
          | exact superpose b6e218 b6e319
          | (have j1 := b6e218 y x
             grind)
          | exact resolve b6e319 b6e218
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e218 b6e319
        have b6e1930 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (k x y) := by
          first
          | (have j1 := b6e1202 x y x
             grind)
          | (have r₁ := b6e1917
             have r₂ := b6e1202 x y x
             grind)
          | exact resolve b6e1917 b6e1202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1202 b6e1917
        have b6e1970 : (M.op y x) = (k x y) := by
          first
          | (have r₁ := b6e1930
             have r₂ := b6e20
             grind)
          | exact resolve b6e1930 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1930
        have b6e30589 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e87 X0 X1 (σ x) (σ y)
             have i₂ := b6e97
             grind)
          | exact superpose b6e97 b6e87
          | (have j0 := b6e87 X0 X1 (σ x) (σ y)
             grind)
          | exact resolve b6e87 b6e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87
        have b6e30783 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (σ (M.op y x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e30589 X0 X1
             have i₂ := b6e1970
             grind)
          | exact superpose b6e1970 b6e30589
          | exact resolve b6e30589 b6e1970
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30589
        have b6e30802 : ∀ X0 X1 : G, (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (M.op X0 (M.op X1 X1)) ≠ (σ (M.op y x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e30783 X0 X1
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e30783
          | (have j0 := b6e30783 X0 X1
             grind)
          | exact resolve b6e30783 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30783
        have b6e30817 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (M.op X0 (M.op X1 X1)) ≠ (σ (M.op y x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e30802 X0 X1
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e30802
          | (have j0 := b6e30802 X0 X1
             grind)
          | exact resolve b6e30802 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30802
        have b6e30819 : ∀ X0 X1 : G, (σ (M.op y y)) = (σ (k y x)) ∨ (M.op X0 (M.op X1 X1)) ≠ (σ (M.op y x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e30817 X0 X1
             have i₂ := b6e104 y
             grind)
          | exact superpose b6e104 b6e30817
          | (have j0 := b6e30817 X0 X1
             grind)
          | exact resolve b6e30817 b6e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30817
        have b6e149463 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X1)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e109 X0 X1 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e109
          | (have j0 := b6e109 X0 X1 (σ x) (σ y)
             grind)
          | exact resolve b6e109 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e109
        have b6e149491 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X1)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
          intro X0 X1
          first
          | (have j0 := b6e149463 X0 X1
             grind)
          | (have r₁ := b6e149463 x X0
             have r₂ := b6e33 X0 (σ y) x
             grind)
          | exact resolve b6e149463 b6e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33 b6e149463
        have b6e149563 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (σ (k x y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e149491 X0 X1
             have i₂ := b6e97
             grind)
          | exact superpose b6e97 b6e149491
          | exact resolve b6e149491 b6e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e97 b6e149491
        have b6e149610 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (σ (M.op y x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e149563 X0 X1
             have i₂ := b6e1970
             grind)
          | exact superpose b6e1970 b6e149563
          | exact resolve b6e149563 b6e1970
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1970 b6e149563
        have b6e149614 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (M.op X0 (M.op X1 X1)) = (σ (M.op y x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e149610 X0 X1
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e149610
          | (have j0 := b6e149610 X0 X1
             grind)
          | exact resolve b6e149610 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e149610
        have b6e149617 : ∀ X0 X1 : G, (σ (M.op y y)) = (σ (k y x)) ∨ (M.op X0 (M.op X1 X1)) = (σ (M.op y x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e149614 X0 X1
             have i₂ := b6e104 y
             grind)
          | exact superpose b6e104 b6e149614
          | (have j0 := b6e149614 X0 X1
             grind)
          | exact resolve b6e149614 b6e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104 b6e149614
        have b6e149618 : (σ (M.op y y)) = (σ (k y x)) := by
          first
          | (have r₁ := b6e149617 x x
             have r₂ := b6e30819 x x
             grind)
          | exact resolve b6e149617 b6e30819
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30819 b6e149617
        have b6e149627 : (k y x) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e149618
             grind)
          | exact superpose b6e149618 b6e13
          | exact resolve b6e13 b6e149618
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e149618
        have b6e149659 : (M.op y y) = (k y x) := by
          first
          | (have i₁ := b6e149627
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e149627
          | exact resolve b6e149627 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e149627
        have b6e153607 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e221 x y
             have i₂ := b6e149659
             grind)
          | exact superpose b6e149659 b6e221
          | (have j0 := b6e221 x y
             grind)
          | exact resolve b6e221 b6e149659
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e221 b6e149659
        have b6e153609 : (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e153607
             have r₂ := b6e20
             grind)
          | exact resolve b6e153607 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e153607
        have b6e153623 : (M.op y x) = (M.op x x) := by
          first
          | (have r₁ := b6e153609
             have r₂ := b6e21
             grind)
          | exact resolve b6e153609 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e153609
        have b6e154605 : ∀ X0 : G, (M.op X0 X0) = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b6e44 X0 x
             have i₂ := b6e153623
             grind)
          | exact superpose b6e153623 b6e44
          | exact resolve b6e44 b6e153623
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e153623
        have b6e159235 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y y) := by
          intro X0
          first
          | (have i₁ := b6e20
             have i₂ := b6e154605 X0
             grind)
          | exact superpose b6e154605 b6e20
          | (have r₁ := b6e20
             have r₂ := b6e154605 y
             grind)
          | exact resolve b6e20 b6e154605
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e154605
        have b6e159355 : False := by grind
        exact b6e159355
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X2) X2)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b7e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b7e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e36 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X2 (M.op (M.op X0 x) x)
               have i₂ := b7e13 X0 (M.op X1 (M.op (M.op X0 x) x)) x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e47 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e36 x X0 x
               have i₂ := b7e36 x X1 x
               grind)
            | (have i₁ := b7e36 X0 X1 (M.op X0 X0)
               have i₂ := b7e36 X0 (M.op X0 X0) x
               grind)
            | exact superpose b7e36 b7e36
            | exact resolve b7e36 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e102 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e110 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e102 (σ X0)
               grind)
            | exact superpose b7e102 b7e19
            | exact resolve b7e19 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e113 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e110 X0
               have i₂ := b7e102 X0
               grind)
            | exact superpose b7e102 b7e110
            | exact resolve b7e110 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102 b7e110
          have b7e124 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e126 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e124
          have b7e127 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e126
               have r₂ := b7e23
               grind)
            | exact resolve b7e126 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e126
          have b7e132 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e127
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e127
            | exact resolve b7e127 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e127
          have b7e134 : (σ (k x y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e132
               have i₂ := b7e113 x
               grind)
            | exact superpose b7e113 b7e132
            | exact resolve b7e132 b7e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e113 b7e132
          have b7e289 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e134
               grind)
            | exact superpose b7e134 b7e14
            | exact resolve b7e14 b7e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e134
          have b7e290 : (k x y) = (M.op x x) := by
            first
            | (have i₁ := b7e289
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e289
            | exact resolve b7e289 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e289
          have b7e298 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e290
               grind)
            | exact superpose b7e290 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e290
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e290
          have b7e299 : (M.op y x) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e298
               have r₂ := b7e21
               grind)
            | exact resolve b7e298 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e298
          have b7e301 : (M.op y x) = (M.op x x) := by
            first
            | (have r₁ := b7e299
               have r₂ := b7e22
               grind)
            | exact resolve b7e299 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e299
          have b7e328 : ∀ X0 : G, (M.op X0 X0) = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b7e47 X0 x
               have i₂ := b7e301
               grind)
            | exact superpose b7e301 b7e47
            | exact resolve b7e47 b7e301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e301
          have b7e441 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y y) := by
            intro X0
            first
            | (have i₁ := b7e21
               have i₂ := b7e328 X0
               grind)
            | exact superpose b7e328 b7e21
            | (have r₁ := b7e21
               have r₂ := b7e328 y
               grind)
            | exact resolve b7e21 b7e328
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e328
          have b7e449 : False := by grind
          exact b7e449
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X2) X2)) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b8e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b8e35 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X2 (M.op (M.op X0 x) x)
               have i₂ := b8e13 X0 (M.op X1 (M.op (M.op X0 x) x)) x
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e46 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e35 x X0 x
               have i₂ := b8e35 x X1 x
               grind)
            | (have i₁ := b8e35 X0 X1 (M.op X0 X0)
               have i₂ := b8e35 X0 (M.op X0 X0) x
               grind)
            | exact superpose b8e35 b8e35
            | exact resolve b8e35 b8e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e75 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X2 (M.op (M.op X1 X3) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X1 X2 X3
               have i₂ := b8e46 X1 X0
               grind)
            | (have i₁ := b8e13 X1 X2 X3
               have i₂ := b8e46 X0 X1
               grind)
            | exact superpose b8e46 b8e13
            | exact resolve b8e13 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X0
               have i₂ := b8e46 X0 X1
               grind)
            | (have i₁ := b8e16 X1 X1
               have i₂ := b8e46 X0 X1
               grind)
            | exact superpose b8e46 b8e16
            | (have j0 := b8e16 X0 X0
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e46 X1 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e46 X0 X0
               grind)
            | exact resolve b8e16 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46
          have b8e99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e102 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e88 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e107 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e99 (σ X0)
               grind)
            | exact superpose b8e99 b8e19
            | exact resolve b8e19 b8e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e112 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e107 X0
               have i₂ := b8e99 X0
               grind)
            | exact superpose b8e99 b8e107
            | exact resolve b8e107 b8e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99 b8e107
          have b8e153 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ (τ X1)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 (τ X1)
               have i₂ := b8e102 X0 (τ X1)
               grind)
            | exact superpose b8e102 b8e26
            | exact resolve b8e26 b8e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e102
          have b8e156 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e153 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e153
            | exact resolve b8e153 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e153
          have b8e195 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X3) X3)) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X0 X2 X3
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e13 X0 X1 X2
               have i₂ := b8e18 X0 X0
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X1 X0
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e199 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X3 X3)) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e35 X3 X0 X2
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e35 X0 X0 X2
               have i₂ := b8e18 X0 X0
               grind)
            | exact superpose b8e18 b8e35
            | (have j1 := b8e18 X1 X0
               grind)
            | exact resolve b8e35 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e219 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e17 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e17
            | (have j0 := b8e17 X1 X0
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | exact resolve b8e17 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e229 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e219 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e219
          have b8e230 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e229 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e229
          have b8e355 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
            intro X0 X2
            first
            | (have i₁ := b8e156 X2 x
               have i₂ := b8e156 X0 x
               grind)
            | exact superpose b8e156 b8e156
            | exact resolve b8e156 b8e156
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156
          have b8e1573 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X3 X3)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e35 X3 X0 X2
               have i₂ := b8e230 X0 X1
               grind)
            | (have i₁ := b8e35 X0 X1 X2
               have i₂ := b8e230 X1 X1
               grind)
            | exact superpose b8e230 b8e35
            | (have j1 := b8e230 X0 X1
               grind)
            | exact resolve b8e35 b8e230
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1691 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e230 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e230
          have b8e2981 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) ≠ (M.op X3 X3) ∨ (M.op X3 X3) = (M.op X3 X1) ∨ (M.op X1 X1) = (k X1 X3) ∨ (M.op X1 X1) = (M.op X3 X1) ∨ (M.op X1 X3) = (k X3 X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e17 X1 X3
               have i₂ := b8e195 X1 X3 X0 X2
               grind)
            | (have i₁ := b8e17 X2 (M.op (M.op X0 X3) X3)
               have i₂ := b8e195 X0 X1 X2 X3
               grind)
            | exact superpose b8e195 b8e17
            | (have j0 := b8e17 X1 X3
               have j1 := b8e195 X1 X3 X2 X3
               grind)
            | (have r₁ := b8e17 X0 (M.op (M.op X0 X3) X3)
               have r₂ := b8e195 X0 (M.op (M.op X0 X3) X3) (M.op (M.op X0 X3) X3) X3
               grind)
            | (have r₁ := b8e17 X1 X0
               have r₂ := b8e195 X0 X1 X2 X3
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e195 X0 X0 X2 X3
               grind)
            | exact resolve b8e17 b8e195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e195
          have b8e3240 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) ≠ (M.op X3 X3) ∨ (M.op X3 X3) = (M.op X3 X1) ∨ (M.op X1 X1) = (k X1 X3) ∨ (M.op X1 X3) = (k X3 X1) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b8e2981 X0 X1 X2 X3
               have j1 := b8e1691 X1 X3
               grind)
            | (have r₁ := b8e2981 X1 X1 X2 X1
               have r₂ := b8e1691 (M.op (M.op X1 X2) X2) X1
               grind)
            | (have r₁ := b8e2981 (M.op (M.op X1 X2) X2) X1 X2 (M.op (M.op X1 X2) X2)
               have r₂ := b8e1691 (M.op (M.op X1 X2) X2) (M.op (M.op X1 X2) X2)
               grind)
            | (have r₁ := b8e2981 X0 X1 X2 X1
               have r₂ := b8e1691 X1 X1
               grind)
            | exact resolve b8e2981 b8e1691
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1691 b8e2981
          have b8e3274 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op X3 X1) ∨ (M.op X1 X1) = (k X1 X3) ∨ (M.op X1 X3) = (k X3 X1) := by
            intro X1 X3
            first
            | (have j0 := b8e3240 x X1 x X3
               grind)
            | (have r₁ := b8e3240 (M.op (M.op X1 x) x) X1 x (M.op (M.op X1 X3) X3)
               have r₂ := b8e75 (M.op (M.op X1 x) x) X1 (M.op (M.op X1 X3) X3) X3
               grind)
            | (have r₁ := b8e3240 x X1 X3 x
               have r₂ := b8e75 x X1 x X3
               grind)
            | exact resolve b8e3240 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75 b8e3240
          have b8e68749 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b8e23
               have i₂ := b8e199 (σ y) (σ x) X0 X1
               grind)
            | exact superpose b8e199 b8e23
            | (have j1 := b8e199 (σ y) (σ x) x x
               grind)
            | exact resolve b8e23 b8e199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e199
          have b8e69841 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            intro X0 X1
            first
            | (have j0 := b8e68749 X0 X1
               grind)
            | (have r₁ := b8e68749 X0 X1
               have r₂ := b8e24
               grind)
            | exact resolve b8e68749 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68749
          have b8e69913 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e69841 x x
               have r₂ := b8e35 x (σ y) x
               grind)
            | exact resolve b8e69841 b8e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69841
          have b8e69919 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e69913
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e69913
            | exact resolve b8e69913 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69913
          have b8e69927 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e69919
               grind)
            | exact superpose b8e69919 b8e23
            | exact resolve b8e23 b8e69919
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69919
          have b8e70003 : (σ (M.op y y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e69927
               have i₂ := b8e112 y
               grind)
            | exact superpose b8e112 b8e69927
            | exact resolve b8e69927 b8e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69927
          have b8e72119 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b8e70003
               have i₂ := b8e3274 x y
               grind)
            | exact superpose b8e3274 b8e70003
            | (have j1 := b8e3274 x y
               grind)
            | exact resolve b8e70003 b8e3274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3274 b8e70003
          have b8e72124 : (M.op y x) = (M.op y y) ∨ (M.op x y) = (k y x) := by
            first
            | (have r₁ := b8e72119
               have r₂ := b8e355 y x
               grind)
            | (have r₁ := b8e72119
               have r₂ := b8e355 x y
               grind)
            | exact resolve b8e72119 b8e355
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e355 b8e72119
          have b8e72132 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b8e72124
               have r₂ := b8e21
               grind)
            | exact resolve b8e72124 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72124
          have b8e91142 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e24
               have i₂ := b8e1573 (σ x) (σ y) X0 X1
               grind)
            | exact superpose b8e1573 b8e24
            | (have j1 := b8e1573 (σ x) (σ y) x x
               grind)
            | exact resolve b8e24 b8e1573
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1573
          have b8e92538 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e91142 x x
               have r₂ := b8e35 x (σ y) x
               grind)
            | exact resolve b8e91142 b8e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35 b8e91142
          have b8e92624 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b8e92538
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e92538
            | exact resolve b8e92538 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92538
          have b8e92635 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b8e92624
               have i₂ := b8e72132
               grind)
            | exact superpose b8e72132 b8e92624
            | exact resolve b8e92624 b8e72132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92624
          have b8e92639 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b8e92635
               have i₂ := b8e112 y
               grind)
            | exact superpose b8e112 b8e92635
            | exact resolve b8e92635 b8e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e112 b8e92635
          have b8e92643 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e92639
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e92639
            | exact resolve b8e92639 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92639
          have b8e92645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e92643
               have i₂ := b8e72132
               grind)
            | exact superpose b8e72132 b8e92643
            | exact resolve b8e92643 b8e72132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72132 b8e92643
          have b8e92646 : (σ (M.op x y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e92645
               have r₂ := b8e20
               grind)
            | exact resolve b8e92645 b8e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92645
          have b8e92647 : (M.op x y) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b8e14 (M.op x y)
               have i₂ := b8e92646
               grind)
            | exact superpose b8e92646 b8e14
            | exact resolve b8e14 b8e92646
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92646
          have b8e92680 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e92647
               have i₂ := b8e14 (M.op y y)
               grind)
            | exact superpose b8e14 b8e92647
            | exact resolve b8e92647 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92647
          have b8e92687 : False := by grind
          exact b8e92687

/-- `Equation3480`: `x ◇ x = y ◇ ((x ◇ z) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3480 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3480 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3480.models_iff G M).mp hM
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
        have b1e65 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e70 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e65
        have b1e71 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e70
             have r₂ := b1e23
             grind)
          | exact resolve b1e70 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70
        have b1e72 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e71
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e71
          | exact resolve b1e71 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71
        have b1e73 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e72
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e72
          | exact resolve b1e72 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e72
        have b1e74 : False := by grind
        exact b1e74
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
        have b2e82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e1478 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e82 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e48474 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1478 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e1478
          | (have j0 := b2e1478 x y
             grind)
          | exact resolve b2e1478 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e1478
        have b2e48487 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e48474
        have b2e48509 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e48487
             have r₂ := b2e22
             grind)
          | exact resolve b2e48487 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48487
        have b2e48519 : False := by grind
        exact b2e48519
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
        have b3e53 : x = y ∨ x = (k x y) := by grind
        clear b3e50
        have b3e54 : x = (k x y) := by
          first
          | (have r₁ := b3e53
             have r₂ := b3e23
             grind)
          | exact resolve b3e53 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e53
        have b3e57 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e54
             grind)
          | exact superpose b3e54 b3e29
          | exact resolve b3e29 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e54
        have b3e58 : False := by grind
        exact b3e58
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
          have b5e63 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e68 : x = y ∨ x = (k x y) := by grind
          clear b5e63
          have b5e69 : x = (k x y) := by
            first
            | (have r₁ := b5e68
               have r₂ := b5e25
               grind)
            | exact resolve b5e68 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e68
          have b5e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e1285 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e72 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72
          have b5e50080 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1285 x y
               have i₂ := b5e69
               grind)
            | exact superpose b5e69 b5e1285
            | (have j0 := b5e1285 x y
               grind)
            | exact resolve b5e1285 b5e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69 b5e1285
          have b5e50091 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e50080
          have b5e50106 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e50091
               have r₂ := b5e24
               grind)
            | exact resolve b5e50091 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50091
          have b5e50110 : False := by grind
          exact b5e50110
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
        have b6e71 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
        have b6e73 : y = (M.op x y) ∨ x = (M.op x y) := by grind
        clear b6e71
        have b6e76 : x = (M.op x y) := by
          first
          | (have r₁ := b6e73
             have r₂ := b6e21
             grind)
          | exact resolve b6e73 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e79 : False := by grind
        exact b6e79
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
          have b7e59 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e64 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e59
          have b7e65 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e25
               grind)
            | exact resolve b7e64 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e64
          have b7e66 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e65
            | exact resolve b7e65 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e69 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e14
            | exact resolve b7e14 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e70 : x = (k x y) := by
            first
            | (have i₁ := b7e69
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e69
            | exact resolve b7e69 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e79 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e70
               grind)
            | exact superpose b7e70 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e80 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b7e79
          have b7e82 : y = (M.op x y) := by
            first
            | (have r₁ := b7e80
               have r₂ := b7e21
               grind)
            | exact resolve b7e80 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80
          have b7e84 : False := by grind
          exact b7e84
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
          have b8e95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e1167 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e95 x y
               grind)
            | exact superpose b8e95 b8e20
            | (have j1 := b8e95 x y
               grind)
            | exact resolve b8e20 b8e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e95
          have b8e1225 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1167
               have r₂ := b8e24
               grind)
            | exact resolve b8e1167 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1167
          have b8e1228 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1225
               have r₂ := b8e23
               grind)
            | exact resolve b8e1225 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1225
          have b8e1229 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1228
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1228
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1228 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1228
          have b8e1230 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e1229
          have b8e1231 : x = (M.op x y) := by
            first
            | (have r₁ := b8e1230
               have r₂ := b8e22
               grind)
            | exact resolve b8e1230 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1230
          have b8e1232 : False := by grind
          exact b8e1232

/-- `Equation3483`: `x ◇ x = y ◇ ((y ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3483 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3483.models_iff G M).mp hM
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
        have b1e51 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e48
        have b1e52 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e51
             have r₂ := b1e23
             grind)
          | exact resolve b1e51 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e53 : (σ y) = (σ (k x y)) := by
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
        have b1e54 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e53
          | exact resolve b1e53 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e53
        have b1e55 : False := by grind
        exact b1e55
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
        have b2e73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e823 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e73 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e73
        have b2e48489 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e823 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e823
          | (have j0 := b2e823 x y
             grind)
          | exact resolve b2e823 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e823
        have b2e48498 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e48489
        have b2e48540 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e48498
             have r₂ := b2e22
             grind)
          | exact resolve b2e48498 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48498
        have b2e48558 : False := by grind
        exact b2e48558
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
        have b3e47 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
        have b3e50 : x = y ∨ y = (k x y) := by grind
        clear b3e47
        have b3e51 : y = (k x y) := by
          first
          | (have r₁ := b3e50
             have r₂ := b3e23
             grind)
          | exact resolve b3e50 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e50
        have b3e54 : (σ x) = (σ y) := by
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
          have b5e47 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e51 : x = y ∨ y = (k x y) := by grind
          clear b5e47
          have b5e53 : y = (k x y) := by
            first
            | (have r₁ := b5e51
               have r₂ := b5e25
               grind)
            | exact resolve b5e51 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e51
          have b5e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e870 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e57 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e48274 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e870 x y
               have i₂ := b5e53
               grind)
            | exact superpose b5e53 b5e870
            | (have j0 := b5e870 x y
               grind)
            | exact resolve b5e870 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53 b5e870
          have b5e48283 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e48274
          have b5e48286 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e48283
               have r₂ := b5e24
               grind)
            | exact resolve b5e48283 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48283
          have b5e48303 : False := by grind
          exact b5e48303
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
        have b6e69 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
        have b6e71 : x = (M.op x y) ∨ y = (M.op x y) := by grind
        clear b6e69
        have b6e74 : y = (M.op x y) := by
          first
          | (have r₁ := b6e71
             have r₂ := b6e21
             grind)
          | exact resolve b6e71 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e77 : False := by grind
        exact b6e77
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
          have b7e57 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e62 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e57
          have b7e63 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e25
               grind)
            | exact resolve b7e62 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e62
          have b7e64 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e63
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e63
            | exact resolve b7e63 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e67 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e64
               grind)
            | exact superpose b7e64 b7e14
            | exact resolve b7e14 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e68 : y = (k x y) := by
            first
            | (have i₁ := b7e67
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e67
            | exact resolve b7e67 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e77 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e78 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b7e77
          have b7e80 : x = (M.op x y) := by
            first
            | (have r₁ := b7e78
               have r₂ := b7e21
               grind)
            | exact resolve b7e78 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e82 : False := by grind
          exact b7e82
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
          have b8e84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e639 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e84 x y
               grind)
            | exact superpose b8e84 b8e20
            | (have j1 := b8e84 x y
               grind)
            | exact resolve b8e20 b8e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84
          have b8e684 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e639
               have r₂ := b8e24
               grind)
            | exact resolve b8e639 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e639
          have b8e687 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e684
               have r₂ := b8e23
               grind)
            | exact resolve b8e684 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e684
          have b8e723 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e687
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e687
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e687 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e687
          have b8e724 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e723
          have b8e725 : y = (M.op x y) := by
            first
            | (have r₁ := b8e724
               have r₂ := b8e22
               grind)
            | exact resolve b8e724 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e724
          have b8e726 : False := by grind
          exact b8e726

/-- `Equation3487`: `x ◇ x = y ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3487 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3487 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3487.models_iff G M).mp hM
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
        have b1e53 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e57 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e53
        have b1e58 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e57
             have r₂ := b1e23
             grind)
          | exact resolve b1e57 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57
        have b1e59 : (σ x) = (σ (k x y)) := by
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
        have b1e60 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e59
          | exact resolve b1e59 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e59
        have b1e61 : False := by grind
        exact b1e61
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
        have b2e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e1474 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e16042 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1474 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e1474
          | (have j0 := b2e1474 x y
             grind)
          | exact resolve b2e1474 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e1474
        have b2e16054 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e16042
        have b2e16071 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e16054
             have r₂ := b2e22
             grind)
          | exact resolve b2e16054 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16054
        have b2e16076 : False := by grind
        exact b2e16076
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
        have b3e47 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
        clear b3e47
        have b3e51 : x = (k x y) := by
          first
          | (have r₁ := b3e50
             have r₂ := b3e23
             grind)
          | exact resolve b3e50 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e50
        have b3e54 : (σ x) = (σ y) := by
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
          have b5e49 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e54 : x = y ∨ x = (k x y) := by grind
          clear b5e49
          have b5e55 : x = (k x y) := by
            first
            | (have r₁ := b5e54
               have r₂ := b5e25
               grind)
            | exact resolve b5e54 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e54
          have b5e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e1466 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e58 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e15195 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1466 x y
               have i₂ := b5e55
               grind)
            | exact superpose b5e55 b5e1466
            | (have j0 := b5e1466 x y
               grind)
            | exact resolve b5e1466 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55 b5e1466
          have b5e15206 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e15195
          have b5e15246 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e15206
               have r₂ := b5e24
               grind)
            | exact resolve b5e15206 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15206
          have b5e15256 : False := by grind
          exact b5e15256
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
        have b6e53 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
        have b6e55 : y = (M.op x y) ∨ x = (M.op x y) := by grind
        clear b6e53
        have b6e58 : x = (M.op x y) := by
          first
          | (have r₁ := b6e55
             have r₂ := b6e21
             grind)
          | exact resolve b6e55 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e61 : False := by grind
        exact b6e61
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
          have b7e42 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          clear b7e42
          have b7e46 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e45
               have r₂ := b7e25
               grind)
            | exact resolve b7e45 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e45
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
          have b7e61 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
          have b7e62 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b7e61
          have b7e64 : y = (M.op x y) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e21
               grind)
            | exact resolve b7e62 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e66 : False := by grind
          exact b7e66
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
          have b8e49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e684 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e49 x y
               grind)
            | exact superpose b8e49 b8e20
            | (have j1 := b8e49 x y
               grind)
            | exact resolve b8e20 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49
          have b8e729 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e684
               have r₂ := b8e24
               grind)
            | exact resolve b8e684 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e684
          have b8e732 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e729
               have r₂ := b8e23
               grind)
            | exact resolve b8e729 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e729
          have b8e733 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e732
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e732
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e732 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e732
          have b8e734 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e733
          have b8e735 : x = (M.op x y) := by
            first
            | (have r₁ := b8e734
               have r₂ := b8e22
               grind)
            | exact resolve b8e734 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e734
          have b8e736 : False := by grind
          exact b8e736

/-- `Equation3487`: `x ◇ x = y ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pxy_pyx_Equation3487 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3487 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3487.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X2) X0)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e33 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 (M.op (M.op X2 x) X0)
           have i₂ := b0e11 X0 X2 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e160 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e33 y X0 X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e33
        | exact resolve b0e33 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e200 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0)) = (M.op X2 (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 (M.op (M.op X1 X1) X0) X2 x
           have i₂ := b0e33 X1 X0 (M.op X2 x)
           grind)
        | exact superpose b0e33 b0e11
        | exact resolve b0e11 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e201 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
        intro X0 X2
        first
        | (have i₁ := b0e200 X0 x X2
           have i₂ := b0e33 x X0 (M.op (M.op x x) X0)
           grind)
        | exact superpose b0e33 b0e200
        | exact resolve b0e200 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e200
      have b0e238 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e160 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e160
        | exact resolve b0e160 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e160
      have b0e403 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e201 (σ y) x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e201
        | exact resolve b0e201 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e201
      have b0e523 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e403 (σ x)
           grind)
        | exact superpose b0e403 b0e18
        | exact resolve b0e18 b0e403
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e403
      have b0e531 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e523
           have i₂ := b0e238 x
           grind)
        | exact superpose b0e238 b0e523
        | exact resolve b0e523 b0e238
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e238 b0e523
      have b0e532 : False := by grind
      exact b0e532
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
        have b1e26 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b1e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e80 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e21
             have i₂ := b1e17 (σ y) X0
             grind)
          | exact superpose b1e17 b1e21
          | (have j1 := b1e17 X0 X0
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e17 X0 (σ y)
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e17 (σ y) x
             grind)
          | exact resolve b1e21 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e86 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e80 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80
        have b1e100 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e27 X0 y
             have i₂ := b1e26 (τ X0)
             grind)
          | exact superpose b1e26 b1e27
          | exact resolve b1e27 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e27
        have b1e108 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e100 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e100
          | exact resolve b1e100 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e100
        have b1e422 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e108 (σ y)
             have i₂ := b1e86 (σ y)
             grind)
          | exact superpose b1e86 b1e108
          | (have j1 := b1e86 (σ y)
             grind)
          | exact resolve b1e108 b1e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e86 b1e108
        have b1e427 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b1e422
        have b1e431 : False := by grind
        exact b1e431
      · have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
        have b2e24 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23
        have b2e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e48 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e25 X0 y
             have i₂ := b2e24 (τ X0)
             grind)
          | exact superpose b2e24 b2e25
          | exact resolve b2e25 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e25
        have b2e52 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e48 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e48
          | exact resolve b2e48 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e65 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (σ y)
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ y) x
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e83 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have j0 := b2e65 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e87 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e83 X0
             have i₂ := b2e52 X0
             grind)
          | exact superpose b2e52 b2e83
          | (have j0 := b2e83 X0
             grind)
          | exact resolve b2e83 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e83
        have b2e200 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have j0 := b2e87 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87
        have b2e201 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e200
        have b2e206 : False := by grind
        exact b2e206
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
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
        have b3e25 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b3e24 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e30 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e25 (σ X0)
             grind)
          | exact superpose b3e25 b3e18
          | exact resolve b3e18 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e33 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e13 (k X0 y)
             have i₂ := b3e30 X0
             grind)
          | exact superpose b3e30 b3e13
          | exact resolve b3e13 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e34 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e33 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e33
          | exact resolve b3e33 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e68 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e16 X0 X1
             have i₂ := b3e17 X2 X0
             grind)
          | exact superpose b3e17 b3e16
          | (have j0 := b3e16 X0 X1
             have j1 := b3e17 X1 X1
             grind)
          | (have r₁ := b3e16 X1 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | exact resolve b3e16 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e87 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e68 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e3057 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e87 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e87
        have b3e3058 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e3057 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3057
        have b3e3059 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e3058 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3058
        have b3e5749 : y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e34 y
             have i₂ := b3e3059 y
             grind)
          | exact superpose b3e3059 b3e34
          | (have j1 := b3e3059 y
             grind)
          | exact resolve b3e34 b3e3059
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e3059
        have b3e5754 : y = (M.op y y) := by grind
        clear b3e5749
        have b3e5794 : False := by grind
        exact b3e5794
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y y) := by grind
          have b4e22 : x = (M.op x x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e49 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b4e17 x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 x X0
               grind)
            | (have r₁ := b4e17 x x
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e50 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e17 (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 (σ x) X0
               grind)
            | (have r₁ := b4e17 (σ x) x
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e53 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e50 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e54 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op x X0) = (k x X0) := by
            intro X0
            first
            | (have j0 := b4e49 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49
          have b4e501 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 x X0
               have i₂ := b4e53 (σ X0)
               grind)
            | exact superpose b4e53 b4e19
            | (have j1 := b4e53 (σ X0)
               grind)
            | exact resolve b4e19 b4e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53
          have b4e29639 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e501 y
               grind)
            | exact superpose b4e501 b4e23
            | (have j1 := b4e501 y
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e501 y
               grind)
            | exact resolve b4e23 b4e501
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e501
          have b4e29723 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
          clear b4e29639
          have b4e29809 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e29723
               grind)
            | exact superpose b4e29723 b4e20
            | exact resolve b4e20 b4e29723
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29723
          have b4e30908 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e29809
               have i₂ := b4e54 y
               grind)
            | exact superpose b4e54 b4e29809
            | (have j1 := b4e54 y
               grind)
            | exact resolve b4e29809 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54 b4e29809
          have b4e30918 : y = (M.op y y) := by grind
          clear b4e30908
          have b4e30922 : False := by grind
          exact b4e30922
        · have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op x x) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e16 X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 X0 x
               grind)
            | (have r₁ := b5e16 X0 x
               have r₂ := b5e22
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e26 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have j0 := b5e25 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25
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
          have b5e30 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 x
               have i₂ := b5e26 (τ X0)
               grind)
            | exact superpose b5e26 b5e27
            | exact resolve b5e27 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e27
          have b5e34 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e30 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e30
            | exact resolve b5e30 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e72 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ x) X0
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 X0
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 X0 (σ x)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) x
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e78 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b5e72 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72
          have b5e387 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e34 (σ x)
               have i₂ := b5e78 (σ x)
               grind)
            | exact superpose b5e78 b5e34
            | (have j1 := b5e78 (σ x)
               grind)
            | exact resolve b5e34 b5e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e78
          have b5e391 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e387
          have b5e396 : False := by grind
          exact b5e396
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
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
        have b6e24 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b6e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e28 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e24 (σ X0)
             have i₂ := b6e18 X0 y
             grind)
          | exact superpose b6e18 b6e24
          | exact resolve b6e24 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e31 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b6e13 (k X0 y)
             have i₂ := b6e28 X0
             grind)
          | exact superpose b6e28 b6e13
          | exact resolve b6e13 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e32 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e31 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e31
          | exact resolve b6e31 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e67 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e16 X0 X1
             have i₂ := b6e17 X2 X0
             grind)
          | exact superpose b6e17 b6e16
          | (have j0 := b6e16 X0 X1
             have j1 := b6e17 X1 X1
             grind)
          | (have r₁ := b6e16 X1 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e16 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | exact resolve b6e16 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e86 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e67 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e2672 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e86 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86
        have b6e2673 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e2672 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2672
        have b6e2674 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e2673 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2673
        have b6e3866 : y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e32 y
             have i₂ := b6e2674 y
             grind)
          | exact superpose b6e2674 b6e32
          | (have j1 := b6e2674 y
             grind)
          | exact resolve b6e32 b6e2674
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32 b6e2674
        have b6e3868 : y = (M.op y y) := by grind
        clear b6e3866
        have b6e3900 : False := by grind
        exact b6e3900
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x x) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e16 X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 X0 (σ x)
               grind)
            | (have r₁ := b7e16 X0 (σ x)
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e26 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have j0 := b7e25 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25
          have b7e30 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 x
               have i₂ := b7e26 (σ X0)
               grind)
            | exact superpose b7e26 b7e19
            | exact resolve b7e19 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e33 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b7e14 (k X0 x)
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e14
            | exact resolve b7e14 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e34 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b7e33 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e33
            | exact resolve b7e33 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e64 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e17 X0 X1
               have i₂ := b7e18 X2 X0
               grind)
            | exact superpose b7e18 b7e17
            | (have j0 := b7e17 X0 X1
               have j1 := b7e18 X1 X1
               grind)
            | (have r₁ := b7e17 X1 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e17 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | exact resolve b7e17 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e86 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b7e64 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e3616 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e86 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e3617 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e3616 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3616
          have b7e3618 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e3617 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3617
          have b7e5114 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e34 x
               have i₂ := b7e3618 x
               grind)
            | exact superpose b7e3618 b7e34
            | (have j1 := b7e3618 x
               grind)
            | exact resolve b7e34 b7e3618
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e3618
          have b7e5116 : x = (M.op x x) := by grind
          clear b7e5114
          have b7e5148 : False := by grind
          exact b7e5148
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y y) := by grind
          have b8e22 : x ≠ (M.op x x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e61 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ y) X0
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ y) x
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e67 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e61 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e234 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 y X0
               have i₂ := b8e67 (σ X0)
               grind)
            | exact superpose b8e67 b8e19
            | (have j1 := b8e67 (σ X0)
               grind)
            | exact resolve b8e19 b8e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e26381 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e234 x
               grind)
            | exact superpose b8e234 b8e20
            | (have j1 := b8e234 x
               grind)
            | exact resolve b8e20 b8e234
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e234
          have b8e26632 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e26381
               have r₂ := b8e24
               grind)
            | exact resolve b8e26381 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26381
          have b8e28922 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e26632
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e26632
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e26632 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26632
          have b8e28935 : x = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e28922
          have b8e28942 : y = (M.op y y) := by
            first
            | (have r₁ := b8e28935
               have r₂ := b8e22
               grind)
            | exact resolve b8e28935 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28935
          have b8e28943 : False := by grind
          exact b8e28943

/-- `Equation3487`: `x ◇ x = y ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_pxy_pyx_Equation3487 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3487 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3487.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e72 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e77 : False := by grind
      exact b0e77
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
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
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : x = (M.op x x) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e46 : ∀ X0 : G, x ≠ x ∨ x = X0 ∨ (M.op x X0) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b4e17 x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 x X0
               grind)
            | (have r₁ := b4e17 x x
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e47 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e17 (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 (σ x) X0
               grind)
            | (have r₁ := b4e17 (σ x) x
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e50 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have j0 := b4e47 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47
          have b4e51 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ x = X0 := by
            intro X0
            first
            | (have j0 := b4e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e282 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k x X0)) ∨ (σ X0) = (σ x) := by
            intro X0
            first
            | (have i₁ := b4e19 x X0
               have i₂ := b4e50 (σ X0)
               grind)
            | exact superpose b4e50 b4e19
            | (have j1 := b4e50 (σ X0)
               grind)
            | exact resolve b4e19 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e14815 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e282 y
               grind)
            | exact superpose b4e282 b4e20
            | (have j1 := b4e282 y
               grind)
            | exact resolve b4e20 b4e282
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e282
          have b4e14847 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b4e14815
               have r₂ := b4e23
               grind)
            | exact resolve b4e14815 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14815
          have b4e14864 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b4e14847
               have i₂ := b4e51 y
               grind)
            | exact superpose b4e51 b4e14847
            | (have j1 := b4e51 y
               grind)
            | exact resolve b4e14847 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51 b4e14847
          have b4e14869 : x = y := by grind
          clear b4e14864
          have b4e14871 : False := by grind
          exact b4e14871
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op x x) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e92 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e30 x
               grind)
            | exact superpose b5e30 b5e24
            | exact resolve b5e24 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e99 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e92
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e92
            | exact resolve b5e92 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e92
          have b5e100 : False := by grind
          exact b5e100
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x x) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e77 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e24
            | exact resolve b7e24 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e101 : (M.op x x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e14
            | exact resolve b7e14 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e102 : x = (M.op x x) := by
            first
            | (have i₁ := b7e101
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e101
            | exact resolve b7e101 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101
          have b7e106 : False := by grind
          exact b7e106
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X2) X0)) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
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
          have b8e34 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X2 (M.op (M.op X2 x) X0)
               have i₂ := b8e13 X0 X2 x
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e59 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e18 (σ X1) (σ X0)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X1) (M.op (σ X1) (σ X1))
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e59 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e59
            | (have j0 := b8e59 X0 X1
               grind)
            | exact resolve b8e59 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59
          have b8e108 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op (M.op X1 X1) X0) X2 x
               have i₂ := b8e34 X1 X0 (M.op X2 x)
               grind)
            | exact superpose b8e34 b8e13
            | exact resolve b8e13 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e109 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X2
            first
            | (have i₁ := b8e108 X0 x X2
               have i₂ := b8e34 x X0 (M.op (M.op x x) X0)
               grind)
            | exact superpose b8e34 b8e108
            | exact resolve b8e108 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34 b8e108
          have b8e121 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e109 (σ X0) x
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e109
            | exact resolve b8e109 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e1237 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e68 x y
               grind)
            | exact superpose b8e68 b8e20
            | (have j1 := b8e68 (M.op y y) y
               grind)
            | exact resolve b8e20 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e1269 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e1237
               have r₂ := b8e23
               grind)
            | exact resolve b8e1237 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1237
          have b8e13188 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e1269
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e1269
            | (have j1 := b8e18 y (M.op y y)
               grind)
            | (have r₁ := b8e1269
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e1269
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e1269 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1269
          have b8e13189 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = y := by grind
          clear b8e13188
          have b8e13191 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have r₁ := b8e13189
               have r₂ := b8e21
               grind)
            | exact resolve b8e13189 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13189
          have b8e13198 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e14 (M.op y y)
               have i₂ := b8e13191
               grind)
            | exact superpose b8e13191 b8e14
            | exact resolve b8e14 b8e13191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13191
          have b8e13237 : y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e13198
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e13198
            | exact resolve b8e13198 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13198
          have b8e13238 : y = (M.op y y) := by grind
          clear b8e13237
          have b8e13291 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b8e109 y x
               have i₂ := b8e13238
               grind)
            | exact superpose b8e13238 b8e109
            | exact resolve b8e109 b8e13238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e109
          have b8e13292 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e121 y x
               have i₂ := b8e13238
               grind)
            | exact superpose b8e13238 b8e121
            | exact resolve b8e121 b8e13238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121 b8e13238
          have b8e15210 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e13292 (σ x)
               grind)
            | exact superpose b8e13292 b8e20
            | exact resolve b8e20 b8e13292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13292
          have b8e15228 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b8e15210
               have i₂ := b8e13291 x
               grind)
            | exact superpose b8e13291 b8e15210
            | exact resolve b8e15210 b8e13291
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13291 b8e15210
          have b8e15229 : False := by grind
          exact b8e15229
