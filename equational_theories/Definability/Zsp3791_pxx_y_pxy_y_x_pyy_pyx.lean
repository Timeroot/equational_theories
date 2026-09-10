import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3791`: `x ◇ y = (z ◇ x) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_x_pyy_pyx_Equation3791 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3791 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3791.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op x x) := by grind
        have b0e21 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b0e22 : x = (M.op y y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e38 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b0e12 x X0 x
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e12
          | exact resolve b0e12 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e45 : y = (M.op y y) := by
          first
          | (have i₁ := b0e38 x
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e38
          | exact resolve b0e38 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e38
        have b0e49 : x = y := by
          first
          | (have i₁ := b0e45
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e45
          | exact resolve b0e45 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e45
        have b0e58 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e49
             grind)
          | exact superpose b0e49 b0e19
          | exact resolve b0e19 b0e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e49
        have b0e62 : (σ y) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e58
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e58
          | exact resolve b0e58 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e58
        have b0e63 : False := by grind
        exact b0e63
      · rcases eq_or_ne (M.op y x) (x) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b1e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b1e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b1e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b1e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e21 : y = (M.op x x) := by grind
          have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
          have b1e23 : x ≠ (M.op y y) := by grind
          have b1e24 : x = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b1e19 (τ X0) X1
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e19
            | exact resolve b1e19 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e19 X1 (τ X0)
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e19
            | exact resolve b1e19 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e35 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b1e14 (k (τ X0) X1)
               have i₂ := b1e29 X0 X1
               grind)
            | exact superpose b1e29 b1e14
            | exact resolve b1e14 b1e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e37 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b1e13 x X0 x
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e13
            | exact resolve b1e13 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e38 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b1e13 x X0 y
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e13
            | exact resolve b1e13 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e39 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b1e13 (σ x) X0 (σ x)
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e13
            | exact resolve b1e13 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e13 (M.op X1 X2) X3 (M.op X2 X0)
               have i₂ := b1e13 X0 X1 X2
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e41 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op x X0) y) := by
            intro X0
            first
            | (have i₁ := b1e13 X0 x x
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e13
            | exact resolve b1e13 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e42 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x X0) x) := by
            intro X0
            first
            | (have i₁ := b1e13 X0 y x
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e13
            | exact resolve b1e13 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e43 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op (σ x) X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b1e13 X0 (σ x) (σ x)
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e13
            | exact resolve b1e13 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e44 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op (M.op X1 X3) X2) (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e13 X2 (M.op X3 X0) (M.op X1 X3)
               have i₂ := b1e13 X0 X1 X3
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e45 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            grind
          have b1e46 : y = (M.op y y) := by
            first
            | (have i₁ := b1e37 x
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e37
            | exact resolve b1e37 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e47 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b1e37 y
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e37
            | exact resolve b1e37 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e51 : x = (M.op x y) := by
            first
            | (have i₁ := b1e47
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e47
            | exact resolve b1e47 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e47
          have b1e53 : x ≠ x ∨ x = (M.op y y) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b1e17 y x
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e17
            | (have j0 := b1e17 y x
               grind)
            | (have r₁ := b1e17 y x
               have r₂ := b1e24
               grind)
            | exact resolve b1e17 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e57 : x = (M.op y y) ∨ (M.op x x) = (k y x) := by grind
          clear b1e53
          have b1e59 : (M.op x x) = (k y x) := by
            first
            | (have r₁ := b1e57
               have r₂ := b1e23
               grind)
            | exact resolve b1e57 b1e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e57
          have b1e60 : y = (k y x) := by
            first
            | (have i₁ := b1e59
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e59
            | exact resolve b1e59 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e59
          have b1e67 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b1e19 X1 X0
               have i₂ := b1e18 (σ X1) (σ X0)
               grind)
            | exact superpose b1e18 b1e19
            | (have j1 := b1e18 (σ X1) (σ X0)
               grind)
            | exact resolve b1e19 b1e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e73 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X2 X1) X0) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e13 X1 X2 X2
               have i₂ := b1e18 X2 X0
               grind)
            | (have i₁ := b1e13 X0 X1 X2
               have i₂ := b1e18 X0 (M.op X1 X2)
               grind)
            | exact superpose b1e18 b1e13
            | (have j1 := b1e18 X2 X0
               grind)
            | exact resolve b1e13 b1e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e77 : x ≠ y := by
            first
            | (have i₁ := b1e23
               have i₂ := b1e46
               grind)
            | exact superpose b1e46 b1e23
            | exact resolve b1e23 b1e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e80 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b1e13 y X0 y
               have i₂ := b1e46
               grind)
            | exact superpose b1e46 b1e13
            | exact resolve b1e13 b1e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e83 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op x X0) (M.op X1 x)) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 (M.op X0 y) X1 x
               have i₂ := b1e38 X0
               grind)
            | exact superpose b1e38 b1e13
            | exact resolve b1e13 b1e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e84 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e83 X0 X1
               have i₂ := b1e13 X0 X1 x
               grind)
            | exact superpose b1e13 b1e83
            | exact resolve b1e83 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e83
          have b1e92 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op (M.op y X1) (M.op X0 x)) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X1 (M.op x X0) y
               have i₂ := b1e41 X0
               grind)
            | exact superpose b1e41 b1e13
            | exact resolve b1e13 b1e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e41
          have b1e105 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b1e37 (M.op x X0)
               have i₂ := b1e42 X0
               grind)
            | exact superpose b1e42 b1e37
            | exact resolve b1e37 b1e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e37
          have b1e111 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b1e105 X0
               have i₂ := b1e80 X0
               grind)
            | exact superpose b1e80 b1e105
            | exact resolve b1e105 b1e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e80 b1e105
          have b1e133 : ∀ X0 X1 : G, (M.op y X1) = (M.op X0 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 y X1 X0
               have i₂ := b1e84 X0 (M.op X1 X0)
               grind)
            | exact superpose b1e84 b1e13
            | exact resolve b1e13 b1e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e139 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 y)) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e13 X2 (M.op X0 y) X1
               have i₂ := b1e84 X0 X1
               grind)
            | exact superpose b1e84 b1e13
            | exact resolve b1e13 b1e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e143 : ∀ X0 X2 : G, (M.op X2 X0) = (M.op X2 (M.op X0 y)) := by
            intro X0 X2
            first
            | (have i₁ := b1e139 X0 x X2
               have i₂ := b1e13 X2 X0 x
               grind)
            | exact superpose b1e13 b1e139
            | exact resolve b1e139 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e139
          have b1e156 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X0) = X0 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b1e45 X0
               have i₂ := b1e18 X0 X1
               grind)
            | (have i₁ := b1e45 X0
               have i₂ := b1e18 X0 (M.op X0 X0)
               grind)
            | exact superpose b1e18 b1e45
            | (have j1 := b1e18 X1 X0
               grind)
            | exact resolve b1e45 b1e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e45
          have b1e178 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op X1 x)) = (M.op (M.op x X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 (M.op x X0) X1 x
               have i₂ := b1e111 X0
               grind)
            | exact superpose b1e111 b1e13
            | exact resolve b1e13 b1e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e179 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op (M.op x X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e178 X0 X1
               have i₂ := b1e92 X1 X0
               grind)
            | exact superpose b1e92 b1e178
            | exact resolve b1e178 b1e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e92 b1e178
          have b1e192 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b1e39 (σ x)
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e39
            | exact resolve b1e39 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e205 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b1e13 (σ y) X0 (σ y)
               have i₂ := b1e192
               grind)
            | exact superpose b1e192 b1e13
            | exact resolve b1e13 b1e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e206 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b1e205 X0
               have i₂ := b1e133 (σ y) X0
               grind)
            | exact superpose b1e133 b1e205
            | exact resolve b1e205 b1e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e205
          have b1e212 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
            first
            | (have i₁ := b1e84 (σ x) (σ y)
               have i₂ := b1e43 y
               grind)
            | exact superpose b1e43 b1e84
            | exact resolve b1e84 b1e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e43
          have b1e222 : (σ y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b1e192
               have i₂ := b1e206 (σ y)
               grind)
            | exact superpose b1e206 b1e192
            | exact resolve b1e192 b1e206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e192
          have b1e228 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op X0 X1) (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X1 (σ y) X0
               have i₂ := b1e206 X0
               grind)
            | exact superpose b1e206 b1e13
            | exact resolve b1e13 b1e206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e230 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op y (σ x))) := by
            first
            | (have i₁ := b1e39 (σ y)
               have i₂ := b1e206 (σ x)
               grind)
            | exact superpose b1e206 b1e39
            | exact resolve b1e39 b1e206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e237 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
            first
            | (have i₁ := b1e230
               have i₂ := b1e39 y
               grind)
            | exact superpose b1e39 b1e230
            | exact resolve b1e230 b1e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e230
          have b1e238 : ∀ X1 : G, (M.op X1 y) = (M.op X1 (σ y)) := by
            intro X1
            first
            | (have i₁ := b1e228 x X1
               have i₂ := b1e13 X1 y x
               grind)
            | exact superpose b1e13 b1e228
            | exact resolve b1e228 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e228
          have b1e244 : (M.op y (σ x)) = (M.op (σ x) y) := by
            first
            | (have i₁ := b1e237
               have i₂ := b1e212
               grind)
            | exact superpose b1e212 b1e237
            | exact resolve b1e237 b1e212
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e237
          have b1e254 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (σ x)) X1) X2) = (M.op (M.op (σ x) X0) (M.op X2 (M.op X1 (σ y)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e40 (σ y) (M.op X0 (σ x)) X1 X2
               have i₂ := b1e39 X0
               grind)
            | exact superpose b1e39 b1e40
            | exact resolve b1e40 b1e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e262 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x (M.op X1 (M.op X0 y))) := by
            intro X0 X1
            first
            | (have i₁ := b1e40 y x X0 X1
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e40
            | exact resolve b1e40 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e281 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op x X0)) X2) = (M.op (M.op x X1) (M.op X2 (M.op X0 y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e40 x X1 (M.op x X0) X2
               have i₂ := b1e42 X0
               grind)
            | exact superpose b1e42 b1e40
            | exact resolve b1e40 b1e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e42
          have b1e285 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X3 X0)) = (M.op (M.op X3 X2) (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e40 X3 X2 X1 (M.op X3 X0)
               have i₂ := b1e13 X0 X1 X3
               grind)
            | exact superpose b1e13 b1e40
            | exact resolve b1e40 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e287 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ y)) = (M.op (M.op (σ x) X1) (M.op (σ x) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b1e40 (σ x) X1 X0 (σ y)
               have i₂ := b1e39 X0
               grind)
            | exact superpose b1e39 b1e40
            | exact resolve b1e40 b1e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e311 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) (M.op (σ x) X0)) = (M.op (M.op X1 X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b1e287 X0 X1
               have i₂ := b1e238 (M.op X1 X0)
               grind)
            | exact superpose b1e238 b1e287
            | exact resolve b1e287 b1e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e287
          have b1e314 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op x X0)) X2) = (M.op X1 (M.op x (M.op X2 (M.op X0 y)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e281 X0 X1 X2
               have i₂ := b1e179 X1 (M.op X2 (M.op X0 y))
               grind)
            | exact superpose b1e179 b1e281
            | exact resolve b1e281 b1e179
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e281
          have b1e326 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b1e262 X0 X1
               have i₂ := b1e143 X0 X1
               grind)
            | (have i₁ := b1e262 X0 x
               have i₂ := b1e143 (M.op X0 y) x
               grind)
            | exact superpose b1e143 b1e262
            | exact resolve b1e262 b1e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e262
          have b1e334 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (σ x)) X1) X2) = (M.op (M.op (σ x) X0) (M.op X2 (M.op X1 y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e254 X0 X1 X2
               have i₂ := b1e238 X1
               grind)
            | exact superpose b1e238 b1e254
            | exact resolve b1e254 b1e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e254
          have b1e340 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op x X0)) X2) = (M.op X1 (M.op x (M.op X2 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e314 X0 X1 X2
               have i₂ := b1e143 X0 X2
               grind)
            | (have i₁ := b1e314 X0 X1 X2
               have i₂ := b1e143 (M.op X0 y) X2
               grind)
            | exact superpose b1e143 b1e314
            | exact resolve b1e314 b1e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e314
          have b1e348 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (σ x)) X1) X2) = (M.op (M.op (σ x) X0) (M.op X2 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e334 X0 X1 X2
               have i₂ := b1e143 X1 X2
               grind)
            | (have i₁ := b1e334 X0 X1 X2
               have i₂ := b1e143 (M.op X1 y) X2
               grind)
            | exact superpose b1e143 b1e334
            | exact resolve b1e334 b1e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e334
          have b1e369 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op (M.op y X0) X1) (M.op X2 (σ y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e44 X2 (σ y) X1 X0
               have i₂ := b1e206 X0
               grind)
            | exact superpose b1e206 b1e44
            | exact resolve b1e44 b1e206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e389 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X0)) = (M.op X1 (M.op y X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e44 X2 X0 X1 y
               have i₂ := b1e84 X0 X1
               grind)
            | exact superpose b1e84 b1e44
            | exact resolve b1e44 b1e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e397 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ y))) = (M.op (M.op (M.op X0 X2) X1) (M.op y X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e44 (σ y) X0 X1 X2
               have i₂ := b1e206 X0
               grind)
            | exact superpose b1e206 b1e44
            | exact resolve b1e44 b1e206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e402 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ y))) = (M.op (M.op (M.op (M.op X0 (σ x)) X2) X1) (M.op (σ x) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e44 (σ y) (M.op X0 (σ x)) X1 X2
               have i₂ := b1e39 X0
               grind)
            | exact superpose b1e39 b1e44
            | exact resolve b1e44 b1e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e411 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op x X1) X0) x) := by
            intro X0 X1
            first
            | (have i₁ := b1e44 y x X0 X1
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e44
            | exact resolve b1e44 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e419 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) (M.op (M.op X4 X1) X0)) = (M.op (M.op X4 X3) (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b1e40 X4 X3 X2 (M.op (M.op X4 X1) X0)
               have i₂ := b1e44 X2 X4 X0 X1
               grind)
            | exact superpose b1e44 b1e40
            | exact resolve b1e40 b1e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e44
          have b1e439 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op X1 (M.op x X0)) x) := by
            intro X0 X1
            first
            | (have i₁ := b1e411 X0 X1
               have i₂ := b1e179 X1 X0
               grind)
            | exact superpose b1e179 b1e411
            | exact resolve b1e411 b1e179
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e179 b1e411
          have b1e448 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ y))) = (M.op (M.op X1 X0) (M.op (M.op (M.op X0 (σ x)) X2) (σ x))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e402 X0 X1 X2
               have i₂ := b1e285 (σ x) X0 X1 (M.op (M.op X0 (σ x)) X2)
               grind)
            | (have i₁ := b1e402 X0 X1 X2
               have i₂ := b1e285 X0 X1 (M.op (M.op X0 (σ x)) X2) (σ x)
               grind)
            | exact superpose b1e285 b1e402
            | exact resolve b1e402 b1e285
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e402
          have b1e453 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ y))) = (M.op (M.op y (M.op X0 X2)) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e397 X0 X1 X2
               have i₂ := b1e285 X0 X1 (M.op X0 X2) y
               grind)
            | (have i₁ := b1e397 X1 X2 X2
               have i₂ := b1e285 y X1 X2 (M.op X1 X2)
               grind)
            | exact superpose b1e285 b1e397
            | exact resolve b1e397 b1e285
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e397
          have b1e457 : ∀ X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op y X2)) := by
            intro X1 X2
            first
            | (have i₁ := b1e389 x X1 X2
               have i₂ := b1e13 X1 X2 x
               grind)
            | exact superpose b1e13 b1e389
            | exact resolve b1e389 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e389
          have b1e473 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op X1 (σ y)) (M.op (M.op y X0) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e369 X0 X1 X2
               have i₂ := b1e285 X2 (σ y) X1 (M.op y X0)
               grind)
            | (have i₁ := b1e369 X0 X1 x
               have i₂ := b1e285 (σ y) X1 (M.op y X0) x
               grind)
            | exact superpose b1e285 b1e369
            | exact resolve b1e369 b1e285
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e369
          have b1e481 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X1 (M.op x (M.op x X0))) := by
            intro X0 X1
            first
            | (have i₁ := b1e439 X0 X1
               have i₂ := b1e340 X0 X1 x
               grind)
            | exact superpose b1e340 b1e439
            | exact resolve b1e439 b1e340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e340 b1e439
          have b1e490 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ y))) = (M.op (M.op X1 X0) (M.op (M.op (σ x) X0) (M.op (σ x) X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e448 X0 X1 X2
               have i₂ := b1e348 X0 X2 (σ x)
               grind)
            | exact superpose b1e348 b1e448
            | exact resolve b1e448 b1e348
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e348 b1e448
          have b1e492 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ y))) = (M.op (M.op X0 y) (M.op X1 (M.op X0 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e453 X0 X1 X2
               have i₂ := b1e285 X1 (M.op X0 X2) y X0
               grind)
            | (have i₁ := b1e453 X0 X1 X2
               have i₂ := b1e285 X0 X1 (M.op X0 X2) y
               grind)
            | exact superpose b1e285 b1e453
            | exact resolve b1e453 b1e285
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e285 b1e453
          have b1e506 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op y X1) (M.op X2 (M.op X0 (σ y)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e473 X0 X1 X2
               have i₂ := b1e419 X2 X0 (σ y) X1 y
               grind)
            | (have i₁ := b1e473 X0 x (M.op X1 X2)
               have i₂ := b1e419 (M.op y X0) X1 X2 (σ y) x
               grind)
            | exact superpose b1e419 b1e473
            | exact resolve b1e473 b1e419
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e419 b1e473
          have b1e511 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X1 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b1e481 X0 X1
               have i₂ := b1e111 X0
               grind)
            | exact superpose b1e111 b1e481
            | exact resolve b1e481 b1e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e111 b1e481
          have b1e520 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ y))) = (M.op (M.op X1 X0) (M.op (M.op X0 X2) y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e490 X0 X1 X2
               have i₂ := b1e311 X2 X0
               grind)
            | exact superpose b1e311 b1e490
            | exact resolve b1e490 b1e311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e311 b1e490
          have b1e521 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ y))) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e492 X0 X1 X2
               have i₂ := b1e84 X0 (M.op X1 (M.op X0 X2))
               grind)
            | exact superpose b1e84 b1e492
            | exact resolve b1e492 b1e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e84 b1e492
          have b1e528 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op y X1) (M.op X2 (M.op X0 y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e506 X0 X1 X2
               have i₂ := b1e238 X0
               grind)
            | exact superpose b1e238 b1e506
            | exact resolve b1e506 b1e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e506
          have b1e529 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X1 y)) := by
            intro X0 X1
            first
            | (have i₁ := b1e511 X0 X1
               have i₂ := b1e457 X1 X0
               grind)
            | (have i₁ := b1e511 X0 X1
               have i₂ := b1e457 X1 (M.op y X0)
               grind)
            | exact superpose b1e457 b1e511
            | exact resolve b1e511 b1e457
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e511
          have b1e537 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ y))) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e520 X0 X1 X2
               have i₂ := b1e143 (M.op X0 X2) (M.op X1 X0)
               grind)
            | (have i₁ := b1e520 X0 X1 X2
               have i₂ := b1e143 (M.op (M.op X0 X2) y) (M.op X1 X0)
               grind)
            | exact superpose b1e143 b1e520
            | exact resolve b1e520 b1e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e520
          have b1e538 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 y)) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e521 X0 X1 X2
               have i₂ := b1e238 X2
               grind)
            | exact superpose b1e238 b1e521
            | exact resolve b1e521 b1e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e521
          have b1e541 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e528 X0 X1 X2
               have i₂ := b1e40 y X1 X0 X2
               grind)
            | exact superpose b1e40 b1e528
            | exact resolve b1e528 b1e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e528
          have b1e545 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 y)) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e537 X0 X1 X2
               have i₂ := b1e238 X2
               grind)
            | exact superpose b1e238 b1e537
            | exact resolve b1e537 b1e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e537
          have b1e546 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e538 X0 X1 X2
               have i₂ := b1e143 X2 X1
               grind)
            | (have i₁ := b1e538 X0 X2 X2
               have i₂ := b1e143 (M.op X2 y) X2
               grind)
            | exact superpose b1e143 b1e538
            | exact resolve b1e538 b1e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e538
          have b1e549 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 y)) = (M.op X1 (M.op X0 (M.op X0 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e545 X0 X1 X2
               have i₂ := b1e541 X0 X1 (M.op X0 X2)
               grind)
            | exact superpose b1e541 b1e545
            | exact resolve b1e545 b1e541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e545
          have b1e551 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X0 (M.op X0 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e549 X0 X1 X2
               have i₂ := b1e143 X2 X1
               grind)
            | (have i₁ := b1e549 X0 X2 X2
               have i₂ := b1e143 (M.op X2 y) X2
               grind)
            | exact superpose b1e143 b1e549
            | exact resolve b1e549 b1e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e549
          have b1e572 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e238 (σ x)
               grind)
            | exact superpose b1e238 b1e20
            | exact resolve b1e20 b1e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e579 : (σ y) = (M.op y y) := by
            first
            | (have i₁ := b1e222
               have i₂ := b1e238 y
               grind)
            | exact superpose b1e238 b1e222
            | exact resolve b1e222 b1e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e222 b1e238
          have b1e580 : y = (σ y) := by
            first
            | (have i₁ := b1e579
               have i₂ := b1e46
               grind)
            | exact superpose b1e46 b1e579
            | exact resolve b1e579 b1e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e579
          have b1e587 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b1e572
               have i₂ := b1e244
               grind)
            | exact superpose b1e244 b1e572
            | exact resolve b1e572 b1e244
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e572
          have b1e609 : (σ x) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b1e587
               have i₂ := b1e51
               grind)
            | exact superpose b1e51 b1e587
            | exact resolve b1e587 b1e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e587
          have b1e668 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b1e19 y X0
               have i₂ := b1e580
               grind)
            | exact superpose b1e580 b1e19
            | exact resolve b1e19 b1e580
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e693 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op X0 (σ x)) (σ y)) ∨ (M.op X1 (σ y)) = (k (σ y) X1) ∨ (M.op (σ y) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e73 X1 (M.op X0 (σ x)) (σ y)
               have i₂ := b1e39 X0
               grind)
            | exact superpose b1e39 b1e73
            | (have j0 := b1e73 X1 X1 (σ y)
               grind)
            | exact resolve b1e73 b1e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e73
          have b1e773 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op X1 (σ y)) = (k (σ y) X1) ∨ (M.op (σ y) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e693 X0 X1
               have i₂ := b1e541 (σ x) X0 (σ y)
               grind)
            | exact superpose b1e541 b1e693
            | (have j0 := b1e693 X0 X1
               grind)
            | exact resolve b1e693 b1e541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e693
          have b1e812 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op X0 (M.op y (σ x))) ∨ (M.op X1 (σ y)) = (k (σ y) X1) ∨ (M.op (σ y) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e773 X0 X1
               have i₂ := b1e212
               grind)
            | exact superpose b1e212 b1e773
            | (have j0 := b1e773 X0 X1
               grind)
            | exact resolve b1e773 b1e212
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e773
          have b1e840 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op (σ x) X0) X1) ∨ (M.op X1 (σ y)) = (k (σ y) X1) ∨ (M.op (σ y) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e812 X0 X1
               have i₂ := b1e457 X0 (σ x)
               grind)
            | (have i₁ := b1e812 X1 X1
               have i₂ := b1e457 X1 (M.op y (σ x))
               grind)
            | exact superpose b1e457 b1e812
            | (have j0 := b1e812 X0 X1
               grind)
            | exact resolve b1e812 b1e457
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e457 b1e812
          have b1e854 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (σ x) (M.op X0 X1)) ∨ (M.op X1 (σ y)) = (k (σ y) X1) ∨ (M.op (σ y) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e840 X0 X1
               have i₂ := b1e541 X0 (σ x) X1
               grind)
            | exact superpose b1e541 b1e840
            | (have j0 := b1e840 X0 X1
               grind)
            | exact resolve b1e840 b1e541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e840
          have b1e864 : ∀ X0 X1 : G, (M.op X1 y) = (k y X1) ∨ (M.op X0 (σ x)) = (M.op (σ x) (M.op X0 X1)) ∨ (M.op (σ y) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e854 X0 X1
               have i₂ := b1e580
               grind)
            | exact superpose b1e580 b1e854
            | (have j0 := b1e854 X0 X1
               grind)
            | exact resolve b1e854 b1e580
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e854
          have b1e871 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (σ x) (M.op X0 X1)) ∨ (M.op X1 y) = (k y X1) ∨ (M.op y X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e864 X0 X1
               have i₂ := b1e206 X1
               grind)
            | exact superpose b1e206 b1e864
            | (have j0 := b1e864 X0 X1
               grind)
            | exact resolve b1e864 b1e206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e864
          have b1e1077 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b1e529 X0 y
               have i₂ := b1e46
               grind)
            | exact superpose b1e46 b1e529
            | exact resolve b1e529 b1e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e1106 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op y X1)) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X1 X0 y
               have i₂ := b1e529 (M.op y X1) X0
               grind)
            | exact superpose b1e529 b1e13
            | exact resolve b1e13 b1e529
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e1113 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b1e38 X0
               have i₂ := b1e529 x X0
               grind)
            | exact superpose b1e529 b1e38
            | exact resolve b1e38 b1e529
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e38 b1e529
          have b1e1434 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b1e39 (σ X0)
               have i₂ := b1e67 x X0
               grind)
            | exact superpose b1e67 b1e39
            | (have j1 := b1e67 x X0
               grind)
            | exact resolve b1e39 b1e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e39
          have b1e1471 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) ∨ (M.op y (σ x)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b1e1434 X0
               have i₂ := b1e206 (σ x)
               grind)
            | exact superpose b1e206 b1e1434
            | (have j0 := b1e1434 X0
               grind)
            | exact resolve b1e1434 b1e206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e206 b1e1434
          have b1e2315 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b1e35 X1 (τ X0)
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e35
            | exact resolve b1e35 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e2568 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b1e133 X0 y
               have i₂ := b1e1077 X0
               grind)
            | (have i₁ := b1e133 y X0
               have i₂ := b1e1077 X0
               grind)
            | exact superpose b1e1077 b1e133
            | exact resolve b1e133 b1e1077
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e133
          have b1e2674 : ∀ X0 : G, (M.op X0 X0) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b1e2568 X0
               have i₂ := b1e143 X0 X0
               grind)
            | (have i₁ := b1e2568 x
               have i₂ := b1e143 (M.op x y) x
               grind)
            | exact superpose b1e143 b1e2568
            | exact resolve b1e2568 b1e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e143 b1e2568
          have b1e2704 : ∀ X0 : G, (M.op X0 X0) = y := by
            intro X0
            first
            | (have i₁ := b1e2674 X0
               have i₂ := b1e46
               grind)
            | exact superpose b1e46 b1e2674
            | exact resolve b1e2674 b1e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e46 b1e2674
          have b1e2798 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            by_contra hcon
            push Not at hcon
            have f2798_15 : ∀ X0 : G, (M.op X0 X0) = y := by
              intro X0
              grind
            have f2798_19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have f2798_28 : X0 ≠ (k X0 y) := by grind
            have f2798_31 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              grind
            have f2798_45 : X0 ≠ X0 := by
              first
              | (have i₁ := f2798_28
                 have i₂ := f2798_31 X0
                 grind)
              | exact superpose f2798_31 f2798_28
              | (have r₁ := f2798_28
                 have r₂ := f2798_31 X0
                 grind)
              | exact resolve f2798_28 f2798_31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have f2798_46 : False := by grind
            exact f2798_46
          have b1e2829 : ∀ X0 : G, y = (σ (k X0 X0)) ∨ (σ X0) = y ∨ (σ X0) = y := by
            intro X0
            first
            | (have i₁ := b1e67 X0 X0
               have i₂ := b1e2704 (σ X0)
               grind)
            | exact superpose b1e2704 b1e67
            | exact resolve b1e67 b1e2704
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e67
          have b1e2839 : ∀ X0 : G, y = (σ (k X0 X0)) ∨ (σ X0) = y := by
            intro X0
            first
            | (have j0 := b1e2829 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e2829
          have b1e3122 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op x (M.op (M.op X0 x) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X1 X0 x
               have i₂ := b1e326 X1 (M.op X0 x)
               grind)
            | exact superpose b1e326 b1e13
            | exact resolve b1e13 b1e326
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e326
          have b1e3183 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op x (M.op X0 (M.op x X1))) := by
            intro X0 X1
            first
            | (have i₁ := b1e3122 X0 X1
               have i₂ := b1e541 x X0 X1
               grind)
            | exact superpose b1e541 b1e3122
            | exact resolve b1e3122 b1e541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e3122
          have b1e3223 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e3183 X1 X0
               have i₂ := b1e546 x X1 X0
               grind)
            | exact superpose b1e546 b1e3183
            | exact resolve b1e3183 b1e546
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e546 b1e3183
          have b1e3362 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e17 X1 X0
               have i₂ := b1e3223 X1 X0
               grind)
            | (have i₁ := b1e17 X1 X0
               have i₂ := b1e3223 X0 X1
               grind)
            | exact superpose b1e3223 b1e17
            | (have j0 := b1e17 X1 X0
               grind)
            | exact resolve b1e17 b1e3223
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e3223
          have b1e3428 : ∀ X0 X1 : G, y = X0 ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e3362 X0 X1
               have i₂ := b1e2704 X1
               grind)
            | exact superpose b1e2704 b1e3362
            | (have j0 := b1e3362 X0 X1
               grind)
            | (have r₁ := b1e3362 y y
               have r₂ := b1e2704 y
               grind)
            | exact resolve b1e3362 b1e2704
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e3362
          have b1e3486 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ y = X0 ∨ y = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e3428 X0 X1
               have i₂ := b1e2704 X0
               grind)
            | exact superpose b1e2704 b1e3428
            | (have j0 := b1e3428 X0 X1
               grind)
            | (have r₁ := b1e3428 y y
               have r₂ := b1e2704 y
               grind)
            | exact resolve b1e3428 b1e2704
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e3428
          have b1e5159 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X1 X2) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e40 X0 X1 X2 X2
               have i₂ := b1e551 X2 (M.op X0 X1) X0
               grind)
            | exact superpose b1e551 b1e40
            | exact resolve b1e40 b1e551
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e40 b1e551
          have b1e5194 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e5159 X0 X1 X2
               have i₂ := b1e541 X2 X1 X2
               grind)
            | exact superpose b1e541 b1e5159
            | exact resolve b1e5159 b1e541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e5159
          have b1e5299 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e5194 X0 X1 x
               have i₂ := b1e2704 x
               grind)
            | exact superpose b1e2704 b1e5194
            | exact resolve b1e5194 b1e2704
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e5194
          have b1e5369 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b1e5299 X0 X1
               have i₂ := b1e541 X1 X0 X0
               grind)
            | exact superpose b1e541 b1e5299
            | exact resolve b1e5299 b1e541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e541 b1e5299
          have b1e20547 : ∀ X0 : G, y = (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = y := by
            intro X0
            first
            | (have i₁ := b1e30 X0 (τ X0)
               have i₂ := b1e2839 (τ X0)
               grind)
            | exact superpose b1e2839 b1e30
            | (have j1 := b1e2839 (τ X0)
               grind)
            | exact resolve b1e30 b1e2839
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e30 b1e2839
          have b1e20590 : ∀ X0 : G, y = (k X0 X0) ∨ (σ (τ X0)) = y := by
            intro X0
            first
            | (have i₁ := b1e20547 X0
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e20547
            | (have j0 := b1e20547 X0
               grind)
            | exact resolve b1e20547 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e20547
          have b1e20608 : ∀ X0 : G, y = (k X0 X0) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b1e20590 X0
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e20590
            | (have j0 := b1e20590 X0
               grind)
            | exact resolve b1e20590 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e20590
          have b1e21467 : ∀ X0 : G, (σ y) = (k X0 (σ (τ X0))) ∨ (τ X0) = y := by
            intro X0
            first
            | (have i₁ := b1e29 X0 (τ X0)
               have i₂ := b1e20608 (τ X0)
               grind)
            | exact superpose b1e20608 b1e29
            | (have j1 := b1e20608 (τ X0)
               grind)
            | exact resolve b1e29 b1e20608
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e21475 : ∀ X0 : G, (σ y) = (k X0 X0) ∨ (τ X0) = y := by
            intro X0
            first
            | (have i₁ := b1e21467 X0
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e21467
            | (have j0 := b1e21467 X0
               grind)
            | exact resolve b1e21467 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e21467
          have b1e21484 : ∀ X0 : G, y = (k X0 X0) ∨ (τ X0) = y := by
            intro X0
            first
            | (have i₁ := b1e21475 X0
               have i₂ := b1e580
               grind)
            | exact superpose b1e580 b1e21475
            | (have j0 := b1e21475 X0
               grind)
            | exact resolve b1e21475 b1e580
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e21475
          have b1e22962 : ∀ X0 : G, (σ y) = (k X0 (σ (τ X0))) ∨ y = (τ (τ X0)) := by
            intro X0
            first
            | (have i₁ := b1e29 X0 (τ X0)
               have i₂ := b1e21484 (τ X0)
               grind)
            | exact superpose b1e21484 b1e29
            | (have j1 := b1e21484 (τ X0)
               grind)
            | exact resolve b1e29 b1e21484
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e21484
          have b1e22967 : ∀ X0 : G, (σ y) = (k X0 X0) ∨ y = (τ (τ X0)) := by
            intro X0
            first
            | (have i₁ := b1e22962 X0
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e22962
            | (have j0 := b1e22962 X0
               grind)
            | exact resolve b1e22962 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e22962
          have b1e22978 : ∀ X0 : G, y = (k X0 X0) ∨ y = (τ (τ X0)) := by
            intro X0
            first
            | (have i₁ := b1e22967 X0
               have i₂ := b1e580
               grind)
            | exact superpose b1e580 b1e22967
            | (have j0 := b1e22967 X0
               grind)
            | exact resolve b1e22967 b1e580
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e22967
          have b1e31404 : ∀ X0 X1 : G, (k (τ X0) y) = (τ (k X0 (τ X1))) ∨ y = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e2315 (τ X1) X0
               have i₂ := b1e22978 X1
               grind)
            | exact superpose b1e22978 b1e2315
            | (have j1 := b1e22978 X1
               grind)
            | exact resolve b1e2315 b1e22978
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e2315 b1e22978
          have b1e31408 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 (τ X1))) ∨ y = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e31404 X0 X1
               have i₂ := b1e2798 (τ X0)
               grind)
            | exact superpose b1e2798 b1e31404
            | (have j0 := b1e31404 X0 X1
               grind)
            | exact resolve b1e31404 b1e2798
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e2798 b1e31404
          have b1e173933 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) y) = (k y (σ x)) ∨ (σ x) = (M.op y (σ x)) := by
            first
            | (have i₁ := b1e871 (σ x) (σ x)
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e871
            | (have j0 := b1e871 x (σ x)
               grind)
            | exact resolve b1e871 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e871
          have b1e174284 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) y) = (k y (σ x)) := by
            first
            | (have r₁ := b1e173933
               have r₂ := b1e609
               grind)
            | exact resolve b1e173933 b1e609
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e173933
          have b1e174410 : (σ y) = (M.op y (σ x)) ∨ (M.op (σ x) y) = (k y (σ x)) := by
            first
            | (have i₁ := b1e174284
               have i₂ := b1e212
               grind)
            | exact superpose b1e212 b1e174284
            | exact resolve b1e174284 b1e212
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e212 b1e174284
          have b1e174501 : y = (M.op y (σ x)) ∨ (M.op (σ x) y) = (k y (σ x)) := by
            first
            | (have i₁ := b1e174410
               have i₂ := b1e580
               grind)
            | exact superpose b1e580 b1e174410
            | exact resolve b1e174410 b1e580
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e174410
          have b1e174568 : (M.op (σ x) y) = (σ (k y x)) ∨ y = (M.op y (σ x)) := by
            first
            | (have i₁ := b1e174501
               have i₂ := b1e668 x
               grind)
            | exact superpose b1e668 b1e174501
            | exact resolve b1e174501 b1e668
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e668 b1e174501
          have b1e174615 : (σ y) = (M.op (σ x) y) ∨ y = (M.op y (σ x)) := by
            first
            | (have i₁ := b1e174568
               have i₂ := b1e60
               grind)
            | exact superpose b1e60 b1e174568
            | exact resolve b1e174568 b1e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e60 b1e174568
          have b1e174646 : (σ y) = (M.op y (σ x)) ∨ y = (M.op y (σ x)) := by
            first
            | (have i₁ := b1e174615
               have i₂ := b1e244
               grind)
            | exact superpose b1e244 b1e174615
            | exact resolve b1e174615 b1e244
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e244 b1e174615
          have b1e174669 : y = (M.op y (σ x)) ∨ y = (M.op y (σ x)) := by
            first
            | (have i₁ := b1e174646
               have i₂ := b1e580
               grind)
            | exact superpose b1e580 b1e174646
            | exact resolve b1e174646 b1e580
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e174646
          have b1e174670 : y = (M.op y (σ x)) := by grind
          clear b1e174669
          have b1e174700 : y ≠ (σ x) := by
            first
            | (have i₁ := b1e609
               have i₂ := b1e174670
               grind)
            | exact superpose b1e174670 b1e609
            | exact resolve b1e609 b1e174670
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e609
          have b1e174713 : ∀ X0 : G, (M.op X0 y) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b1e1106 X0 (σ x)
               have i₂ := b1e174670
               grind)
            | exact superpose b1e174670 b1e1106
            | exact resolve b1e1106 b1e174670
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e1106
          have b1e228120 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (M.op (σ x) X0) = (σ (k (τ X0) x)) ∨ (M.op (σ x) X0) = (M.op y (σ x)) := by
            intro X0
            first
            | (have i₁ := b1e1471 (τ X0)
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e1471
            | exact resolve b1e1471 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e228450 : ∀ X0 : G, (M.op y (σ x)) ≠ (σ (k X0 x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) ∨ (M.op y (σ x)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have j0 := b1e1471 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e1471
          have b1e228455 : ∀ X0 : G, y ≠ (σ (k X0 x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) ∨ (M.op y (σ x)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b1e228450 X0
               have i₂ := b1e174670
               grind)
            | exact superpose b1e174670 b1e228450
            | (have j0 := b1e228450 X0
               grind)
            | exact resolve b1e228450 b1e174670
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e228450
          have b1e228507 : ∀ X0 : G, y = (σ x) ∨ (M.op (σ x) X0) = (σ (k (τ X0) x)) ∨ (M.op (σ x) X0) = (M.op y (σ x)) := by
            intro X0
            first
            | (have i₁ := b1e228120 X0
               have i₂ := b1e2704 X0
               grind)
            | exact superpose b1e2704 b1e228120
            | (have j0 := b1e228120 X0
               grind)
            | exact resolve b1e228120 b1e2704
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e228120
          have b1e228515 : ∀ X0 : G, y = (σ x) ∨ y ≠ (σ (k X0 x)) ∨ (M.op y (σ x)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b1e228455 X0
               have i₂ := b1e2704 (σ X0)
               grind)
            | exact superpose b1e2704 b1e228455
            | (have j0 := b1e228455 X0
               grind)
            | exact resolve b1e228455 b1e2704
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e228455
          have b1e228546 : ∀ X0 : G, (M.op (σ x) X0) = (σ (k (τ X0) x)) ∨ (M.op (σ x) X0) = (M.op y (σ x)) := by
            intro X0
            first
            | (have j0 := b1e228507 X0
               grind)
            | (have r₁ := b1e228507 X0
               have r₂ := b1e174700
               grind)
            | exact resolve b1e228507 b1e174700
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e228507
          have b1e228553 : ∀ X0 : G, y ≠ (σ (k X0 x)) ∨ (M.op y (σ x)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have j0 := b1e228515 X0
               grind)
            | (have r₁ := b1e228515 X0
               have r₂ := b1e174700
               grind)
            | exact resolve b1e228515 b1e174700
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e174700 b1e228515
          have b1e228574 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (M.op (σ x) X0) = (M.op y (σ x)) := by
            intro X0
            first
            | (have i₁ := b1e228546 X0
               have i₂ := b1e29 X0 x
               grind)
            | exact superpose b1e29 b1e228546
            | (have j0 := b1e228546 X0
               grind)
            | exact resolve b1e228546 b1e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e228546
          have b1e228581 : ∀ X0 : G, (M.op y (σ x)) = (M.op (σ X0) y) ∨ y ≠ (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b1e228553 X0
               have i₂ := b1e174713 (σ X0)
               grind)
            | exact superpose b1e174713 b1e228553
            | (have j0 := b1e228553 X0
               grind)
            | exact resolve b1e228553 b1e174713
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e228553
          have b1e228595 : ∀ X0 : G, (M.op X0 y) = (k X0 (σ x)) ∨ (M.op (σ x) X0) = (M.op y (σ x)) := by
            intro X0
            first
            | (have i₁ := b1e228574 X0
               have i₂ := b1e174713 X0
               grind)
            | exact superpose b1e174713 b1e228574
            | (have j0 := b1e228574 X0
               grind)
            | exact resolve b1e228574 b1e174713
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e228574
          have b1e228601 : ∀ X0 : G, (M.op y (σ x)) = (M.op y (σ X0)) ∨ y ≠ (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b1e228581 X0
               have i₂ := b1e1077 (σ X0)
               grind)
            | exact superpose b1e1077 b1e228581
            | (have j0 := b1e228581 X0
               grind)
            | exact resolve b1e228581 b1e1077
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e1077 b1e228581
          have b1e228612 : ∀ X0 : G, y = (M.op (σ x) X0) ∨ (M.op X0 y) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b1e228595 X0
               have i₂ := b1e174670
               grind)
            | exact superpose b1e174670 b1e228595
            | (have j0 := b1e228595 X0
               grind)
            | exact resolve b1e228595 b1e174670
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e228595
          have b1e228618 : ∀ X0 : G, y ≠ (σ (k X0 x)) ∨ y = (M.op y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b1e228601 X0
               have i₂ := b1e174670
               grind)
            | exact superpose b1e174670 b1e228601
            | (have j0 := b1e228601 X0
               grind)
            | exact resolve b1e228601 b1e174670
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e174670 b1e228601
          have b1e228629 : ∀ X0 : G, (M.op X0 y) = (k X0 (σ x)) ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b1e228612 X0
               have i₂ := b1e174713 X0
               grind)
            | exact superpose b1e174713 b1e228612
            | (have j0 := b1e228612 X0
               grind)
            | exact resolve b1e228612 b1e174713
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e174713 b1e228612
          have b1e288130 : ∀ X0 : G, (τ (M.op X0 y)) = (k (τ X0) x) ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b1e35 X0 x
               have i₂ := b1e228629 X0
               grind)
            | exact superpose b1e228629 b1e35
            | (have j1 := b1e228629 X0
               grind)
            | exact resolve b1e35 b1e228629
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e35 b1e228629
          have b1e307007 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (τ X1)) ∨ y = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e15 (k X0 (τ X1))
               have i₂ := b1e31408 X0 X1
               grind)
            | exact superpose b1e31408 b1e15
            | (have j1 := b1e31408 X0 X1
               grind)
            | exact resolve b1e15 b1e31408
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e31408
          have b1e307197 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ y = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e307007 X0 X1
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e307007
            | (have j0 := b1e307007 X0 X1
               grind)
            | exact resolve b1e307007 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e307007
          have b1e308526 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ y = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e29 X0 (τ X1)
               have i₂ := b1e307197 (τ X0) X1
               grind)
            | exact superpose b1e307197 b1e29
            | (have j1 := b1e307197 X0 X1
               grind)
            | exact resolve b1e29 b1e307197
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e29 b1e307197
          have b1e308739 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ y = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e308526 X0 X1
               have i₂ := b1e15 X1
               grind)
            | exact superpose b1e15 b1e308526
            | (have j0 := b1e308526 X0 X1
               grind)
            | exact resolve b1e308526 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e308526
          have b1e308817 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ y = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e308739 X0 X1
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e308739
            | (have j0 := b1e308739 X0 X1
               grind)
            | exact resolve b1e308739 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e308739
          have b1e310034 : ∀ X0 : G, y ≠ X0 ∨ y = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b1e308817 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e308817
          have b1e310059 : ∀ X0 : G, y = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b1e310034 X0
               have j1 := b1e20608 X0
               grind)
            | (have r₁ := b1e310034 (k X0 X0)
               have r₂ := b1e20608 X0
               grind)
            | (have r₁ := b1e310034 X0
               have r₂ := b1e20608 X0
               grind)
            | (have r₁ := b1e310034 y
               have r₂ := b1e20608 y
               grind)
            | exact resolve b1e310034 b1e20608
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e20608 b1e310034
          have b1e423466 : (τ x) = (k (τ x) x) ∨ x = y := by
            first
            | (have i₁ := b1e288130 x
               have i₂ := b1e51
               grind)
            | exact superpose b1e51 b1e288130
            | exact resolve b1e288130 b1e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e288130
          have b1e423529 : (τ x) = (k (τ x) x) := by
            first
            | (have r₁ := b1e423466
               have r₂ := b1e77
               grind)
            | exact resolve b1e423466 b1e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e423466
          have b1e428899 : (τ x) = (M.op x (τ x)) ∨ x = (k x x) ∨ x = (M.op (τ x) x) := by
            first
            | (have i₁ := b1e156 x (τ x)
               have i₂ := b1e423529
               grind)
            | exact superpose b1e423529 b1e156
            | (have j0 := b1e156 x (τ x)
               grind)
            | exact resolve b1e156 b1e423529
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e156 b1e423529
          have b1e428900 : x = y ∨ (τ x) = (M.op x (τ x)) ∨ x = (M.op (τ x) x) := by
            first
            | (have i₁ := b1e428899
               have i₂ := b1e310059 x
               grind)
            | exact superpose b1e310059 b1e428899
            | exact resolve b1e428899 b1e310059
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e310059 b1e428899
          have b1e428904 : (τ x) = (M.op x (τ x)) ∨ x = (M.op (τ x) x) := by
            first
            | (have r₁ := b1e428900
               have r₂ := b1e77
               grind)
            | exact resolve b1e428900 b1e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e428900
          have b1e428906 : (τ x) = (M.op x (τ x)) ∨ x = (M.op x (τ x)) := by
            first
            | (have i₁ := b1e428904
               have i₂ := b1e1113 (τ x)
               grind)
            | exact superpose b1e1113 b1e428904
            | exact resolve b1e428904 b1e1113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e1113 b1e428904
          have b1e440239 : (M.op x y) = (M.op (τ x) (τ x)) ∨ x = (M.op x (τ x)) := by
            first
            | (have i₁ := b1e5369 (τ x) x
               have i₂ := b1e428906
               grind)
            | exact superpose b1e428906 b1e5369
            | exact resolve b1e5369 b1e428906
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e5369 b1e428906
          have b1e440265 : y = (M.op x y) ∨ x = (M.op x (τ x)) := by
            first
            | (have i₁ := b1e440239
               have i₂ := b1e2704 (τ x)
               grind)
            | exact superpose b1e2704 b1e440239
            | exact resolve b1e440239 b1e2704
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e2704 b1e440239
          have b1e440337 : x = y ∨ x = (M.op x (τ x)) := by
            first
            | (have i₁ := b1e440265
               have i₂ := b1e51
               grind)
            | exact superpose b1e51 b1e440265
            | exact resolve b1e440265 b1e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e51 b1e440265
          have b1e440386 : x = (M.op x (τ x)) := by
            first
            | (have r₁ := b1e440337
               have r₂ := b1e77
               grind)
            | exact resolve b1e440337 b1e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e440337
          have b1e445574 : x ≠ x ∨ x = y ∨ y = (k (τ x) x) := by
            first
            | (have i₁ := b1e3486 x (τ x)
               have i₂ := b1e440386
               grind)
            | exact superpose b1e440386 b1e3486
            | (have j0 := b1e3486 x (τ x)
               grind)
            | (have r₁ := b1e3486 x (τ x)
               have r₂ := b1e440386
               grind)
            | exact resolve b1e3486 b1e440386
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e3486 b1e440386
          have b1e445603 : x = y ∨ y = (k (τ x) x) := by grind
          clear b1e445574
          have b1e445621 : y = (k (τ x) x) := by
            first
            | (have r₁ := b1e445603
               have r₂ := b1e77
               grind)
            | exact resolve b1e445603 b1e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e445603
          have b1e449421 : y ≠ (σ y) ∨ y = (M.op y (σ (τ x))) := by
            first
            | (have i₁ := b1e228618 (τ x)
               have i₂ := b1e445621
               grind)
            | exact superpose b1e445621 b1e228618
            | (have j0 := b1e228618 (τ x)
               grind)
            | exact resolve b1e228618 b1e445621
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e228618 b1e445621
          have b1e449431 : y = (M.op y (σ (τ x))) := by
            first
            | (have r₁ := b1e449421
               have r₂ := b1e580
               grind)
            | exact resolve b1e449421 b1e580
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e580 b1e449421
          have b1e449435 : y = (M.op y x) := by
            first
            | (have i₁ := b1e449431
               have i₂ := b1e15 x
               grind)
            | exact superpose b1e15 b1e449431
            | exact resolve b1e449431 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e449431
          have b1e449438 : x = y := by
            first
            | (have i₁ := b1e449435
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e449435
            | exact resolve b1e449435 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e449435
          have b1e449441 : False := by grind
          exact b1e449441
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b2e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b2e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b2e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : y = (M.op x x) := by grind
          have b2e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
          have b2e23 : x ≠ (M.op y y) := by grind
          have b2e24 : x ≠ (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 (τ X0) X1
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e19
            | exact resolve b2e19 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 X1 (τ X0)
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e19
            | exact resolve b2e19 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e37 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b2e13 x X0 x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e38 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b2e13 (σ x) X0 (σ x)
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e13
            | exact resolve b2e13 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 (M.op X1 X2) X3 (M.op X2 X0)
               have i₂ := b2e13 X0 X1 X2
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e40 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op x X0) y) := by
            intro X0
            first
            | (have i₁ := b2e13 X0 x x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e42 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op (M.op X1 X3) X2) (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 X2 (M.op X3 X0) (M.op X1 X3)
               have i₂ := b2e13 X0 X1 X3
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e44 : y = (M.op y y) := by
            first
            | (have i₁ := b2e37 x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e37
            | exact resolve b2e37 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e53 : x ≠ y := by
            first
            | (have i₁ := b2e23
               have i₂ := b2e44
               grind)
            | exact superpose b2e44 b2e23
            | exact resolve b2e23 b2e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e55 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op y X0) y) := by
            intro X0
            first
            | (have i₁ := b2e13 X0 y y
               have i₂ := b2e44
               grind)
            | exact superpose b2e44 b2e13
            | exact resolve b2e13 b2e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e56 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b2e13 y X0 y
               have i₂ := b2e44
               grind)
            | exact superpose b2e44 b2e13
            | exact resolve b2e13 b2e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 X1 X0
               have i₂ := b2e18 (σ X1) (σ X0)
               grind)
            | exact superpose b2e18 b2e19
            | (have j1 := b2e18 (σ X1) (σ X0)
               grind)
            | exact resolve b2e19 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e63 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op (τ X1) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b2e29 X1 X0
               have i₂ := b2e18 (τ X1) X0
               grind)
            | exact superpose b2e18 b2e29
            | (have j1 := b2e18 (τ X1) X0
               grind)
            | exact resolve b2e29 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e29
          have b2e67 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X2 X1) X0) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 X1 X2 X2
               have i₂ := b2e18 X2 X0
               grind)
            | (have i₁ := b2e13 X0 X1 X2
               have i₂ := b2e18 X0 (M.op X1 X2)
               grind)
            | exact superpose b2e18 b2e13
            | (have j1 := b2e18 X2 X0
               grind)
            | exact resolve b2e13 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e69 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op (M.op X1 X1) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X1 X1 X1
               have i₂ := b2e18 (M.op X1 X1) X0
               grind)
            | (have i₁ := b2e13 X0 X1 x
               have i₂ := b2e18 X0 (M.op (M.op x X0) (M.op X1 x))
               grind)
            | exact superpose b2e18 b2e13
            | (have j1 := b2e18 (M.op X1 X1) X0
               grind)
            | exact resolve b2e13 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e87 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e14 (k X0 (τ X1))
               have i₂ := b2e30 X1 X0
               grind)
            | exact superpose b2e30 b2e14
            | exact resolve b2e14 b2e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e90 : ∀ X0 : G, (M.op (M.op x X0) y) = (M.op (M.op X0 x) y) := by
            intro X0
            first
            | (have i₁ := b2e55 (M.op X0 x)
               have i₂ := b2e37 X0
               grind)
            | exact superpose b2e37 b2e55
            | exact resolve b2e55 b2e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e93 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op (M.op y X1) (M.op X0 y)) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X1 (M.op y X0) y
               have i₂ := b2e55 X0
               grind)
            | exact superpose b2e55 b2e13
            | exact resolve b2e13 b2e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e55
          have b2e96 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e93 X0 X1
               have i₂ := b2e13 X1 X0 y
               grind)
            | exact superpose b2e13 b2e93
            | exact resolve b2e93 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e93
          have b2e98 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) y) := by
            intro X0
            first
            | (have i₁ := b2e90 X0
               have i₂ := b2e40 X0
               grind)
            | exact superpose b2e40 b2e90
            | exact resolve b2e90 b2e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e90
          have b2e116 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op y X0) (M.op X1 y)) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 (M.op X0 y) X1 y
               have i₂ := b2e56 X0
               grind)
            | exact superpose b2e56 b2e13
            | exact resolve b2e13 b2e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e117 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b2e116 X0 X1
               have i₂ := b2e13 X0 X1 y
               grind)
            | exact superpose b2e13 b2e116
            | exact resolve b2e116 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e116
          have b2e125 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b2e38 (σ x)
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e38
            | exact resolve b2e38 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e135 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b2e13 (σ y) X0 (σ y)
               have i₂ := b2e125
               grind)
            | exact superpose b2e125 b2e13
            | exact resolve b2e13 b2e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e146 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op X1 (M.op X0 y)) := by
            intro X0 X1
            first
            | (have i₁ := b2e96 (M.op X0 y) X1
               have i₂ := b2e56 X0
               grind)
            | exact superpose b2e56 b2e96
            | exact resolve b2e96 b2e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e153 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) (M.op (M.op y X0) X0)) := by
            intro X0
            grind
          have b2e156 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X0)) = (M.op (M.op y X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 (M.op y X1) X2 X0
               have i₂ := b2e96 X1 X0
               grind)
            | exact superpose b2e96 b2e13
            | exact resolve b2e13 b2e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e157 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X1 y X0
               have i₂ := b2e96 X0 (M.op X0 X1)
               grind)
            | exact superpose b2e96 b2e13
            | exact resolve b2e13 b2e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e158 : (M.op (σ x) y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b2e38 y
               have i₂ := b2e96 (σ x) (σ y)
               grind)
            | exact superpose b2e96 b2e38
            | exact resolve b2e38 b2e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e161 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b2e37 y
               have i₂ := b2e96 x y
               grind)
            | exact superpose b2e96 b2e37
            | exact resolve b2e37 b2e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e164 : ∀ X1 X2 : G, (M.op X1 X2) = (M.op (M.op y X1) X2) := by
            intro X1 X2
            first
            | (have i₁ := b2e156 x X1 X2
               have i₂ := b2e13 X1 X2 x
               grind)
            | exact superpose b2e13 b2e156
            | exact resolve b2e156 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e156
          have b2e168 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 y)) := by
            intro X0 X1
            first
            | (have i₁ := b2e146 X0 X1
               have i₂ := b2e96 X0 X1
               grind)
            | exact superpose b2e96 b2e146
            | exact resolve b2e146 b2e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e146
          have b2e187 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op y (M.op X1 (M.op X0 y))) := by
            intro X0 X1
            first
            | (have i₁ := b2e39 y y X0 X1
               have i₂ := b2e44
               grind)
            | exact superpose b2e44 b2e39
            | exact resolve b2e39 b2e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e204 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X3 X0)) = (M.op (M.op X3 X2) (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e39 X3 X2 X1 (M.op X3 X0)
               have i₂ := b2e13 X0 X1 X3
               grind)
            | exact superpose b2e13 b2e39
            | exact resolve b2e39 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e211 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 X2)) = (M.op (M.op X0 X1) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e96 (M.op X1 X2) (M.op X2 X0)
               have i₂ := b2e39 X2 X0 X1 y
               grind)
            | exact superpose b2e39 b2e96
            | exact resolve b2e96 b2e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e222 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) y) := by
            intro X0 X1
            first
            | (have i₁ := b2e211 X0 X1 x
               have i₂ := b2e13 X0 X1 x
               grind)
            | exact superpose b2e13 b2e211
            | exact resolve b2e211 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e211
          have b2e236 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op y (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e187 X0 X1
               have i₂ := b2e168 X0 X1
               grind)
            | exact superpose b2e168 b2e187
            | exact resolve b2e187 b2e168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e187
          have b2e247 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e236 X0 X1
               have i₂ := b2e164 X0 X1
               grind)
            | (have i₁ := b2e236 X0 x
               have i₂ := b2e164 (M.op y X0) x
               grind)
            | exact superpose b2e164 b2e236
            | exact resolve b2e236 b2e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e236
          have b2e256 : x ≠ (M.op x y) := by
            first
            | (have i₁ := b2e24
               have i₂ := b2e161
               grind)
            | exact superpose b2e161 b2e24
            | exact resolve b2e24 b2e161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e261 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) (M.op X1 (M.op X0 y))) := by
            intro X0 X1
            first
            | (have i₁ := b2e39 y x X0 X1
               have i₂ := b2e161
               grind)
            | exact superpose b2e161 b2e39
            | exact resolve b2e39 b2e161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e161
          have b2e268 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x (M.op X1 (M.op X0 y))) := by
            intro X0 X1
            first
            | (have i₁ := b2e261 X0 X1
               have i₂ := b2e117 x (M.op X1 (M.op X0 y))
               grind)
            | exact superpose b2e117 b2e261
            | exact resolve b2e261 b2e117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e261
          have b2e270 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e268 X0 X1
               have i₂ := b2e168 X0 X1
               grind)
            | exact superpose b2e168 b2e268
            | exact resolve b2e268 b2e168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e268
          have b2e277 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) X1) (M.op X2 (M.op x X0))) = (M.op X1 (M.op y X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e42 X2 (M.op x X0) X1 y
               have i₂ := b2e40 X0
               grind)
            | exact superpose b2e40 b2e42
            | exact resolve b2e42 b2e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e281 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) (M.op X1 (σ y))) = (M.op X0 (M.op (σ y) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e42 X1 (σ y) X0 (σ y)
               have i₂ := b2e125
               grind)
            | exact superpose b2e125 b2e42
            | exact resolve b2e42 b2e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e284 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 x) X2)) = (M.op (M.op (M.op x X0) X1) (M.op X2 y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e42 X2 y X1 (M.op X0 x)
               have i₂ := b2e37 X0
               grind)
            | exact superpose b2e37 b2e42
            | exact resolve b2e42 b2e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e291 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 x) (M.op X1 x)) := by
            intro X0 X1
            first
            | (have i₁ := b2e42 X1 x y X0
               have i₂ := b2e40 X0
               grind)
            | exact superpose b2e40 b2e42
            | exact resolve b2e42 b2e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e297 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op (M.op (M.op y X1) X3) X2) (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e42 X0 (M.op y X1) X2 X3
               have i₂ := b2e96 X1 X0
               grind)
            | exact superpose b2e96 b2e42
            | exact resolve b2e42 b2e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e298 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op (M.op X1 X4) X3) X2) (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e42 (M.op X4 X0) (M.op X1 X4) X2 X3
               have i₂ := b2e13 X0 X1 X4
               grind)
            | exact superpose b2e13 b2e42
            | exact resolve b2e42 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e301 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x X0))) = (M.op (M.op (M.op y X2) X1) (M.op X0 x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e42 (M.op x X0) y X1 X2
               have i₂ := b2e40 X0
               grind)
            | exact superpose b2e40 b2e42
            | exact resolve b2e42 b2e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e40
          have b2e307 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op (M.op x X1) X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b2e42 x x X0 X1
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e42
            | exact resolve b2e42 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e308 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 y)) = (M.op (M.op (M.op (M.op X0 x) X2) X1) (M.op x X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e42 y (M.op X0 x) X1 X2
               have i₂ := b2e37 X0
               grind)
            | exact superpose b2e37 b2e42
            | exact resolve b2e42 b2e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e37
          have b2e309 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 y)) = (M.op (M.op (M.op (M.op X0 y) X2) X1) (M.op y X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e42 y (M.op X0 y) X1 X2
               have i₂ := b2e56 X0
               grind)
            | exact superpose b2e56 b2e42
            | exact resolve b2e42 b2e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e56
          have b2e310 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op y X1) X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b2e42 y y X0 X1
               have i₂ := b2e44
               grind)
            | exact superpose b2e44 b2e42
            | exact resolve b2e42 b2e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e315 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) (M.op (M.op X4 X1) X0)) = (M.op (M.op X4 X3) (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e39 X4 X3 X2 (M.op (M.op X4 X1) X0)
               have i₂ := b2e42 X2 X4 X0 X1
               grind)
            | exact superpose b2e42 b2e39
            | exact resolve b2e39 b2e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e332 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 (M.op X1 y)) := by
            intro X0 X1
            first
            | (have i₁ := b2e310 X0 X1
               have i₂ := b2e222 (M.op y X1) X0
               grind)
            | exact superpose b2e222 b2e310
            | exact resolve b2e310 b2e222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e310
          have b2e333 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 y)) = (M.op (M.op y (M.op (M.op X0 y) X2)) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e309 X0 X1 X2
               have i₂ := b2e204 X0 X1 (M.op (M.op X0 y) X2) y
               grind)
            | (have i₁ := b2e309 X1 X2 X2
               have i₂ := b2e204 y X1 X2 (M.op (M.op X1 y) X2)
               grind)
            | exact superpose b2e204 b2e309
            | exact resolve b2e309 b2e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e309
          have b2e334 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 y)) = (M.op (M.op x (M.op (M.op X0 x) X2)) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e308 X0 X1 X2
               have i₂ := b2e204 X0 X1 (M.op (M.op X0 x) X2) x
               grind)
            | (have i₁ := b2e308 X1 X2 X2
               have i₂ := b2e204 x X1 X2 (M.op (M.op X1 x) X2)
               grind)
            | exact superpose b2e204 b2e308
            | exact resolve b2e308 b2e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e308
          have b2e335 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op x X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e307 X0 X1
               have i₂ := b2e222 (M.op x X1) X0
               grind)
            | exact superpose b2e222 b2e307
            | exact resolve b2e307 b2e222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e307
          have b2e339 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x X0))) = (M.op (M.op X1 x) (M.op (M.op y X2) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e301 X0 X1 X2
               have i₂ := b2e204 X0 x X1 (M.op y X2)
               grind)
            | (have i₁ := b2e301 x X1 X2
               have i₂ := b2e204 x X1 (M.op y X2) x
               grind)
            | exact superpose b2e204 b2e301
            | exact resolve b2e301 b2e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e301
          have b2e342 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X0))) = (M.op (M.op X2 X1) (M.op (M.op (M.op X1 X4) X3) X0)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e298 X0 X1 X2 X3 X4
               have i₂ := b2e204 X0 X1 X2 (M.op (M.op X1 X4) X3)
               grind)
            | (have i₁ := b2e298 X3 X0 X1 X3 X4
               have i₂ := b2e204 X0 X1 (M.op (M.op X0 X4) X3) X3
               grind)
            | exact superpose b2e204 b2e298
            | exact resolve b2e298 b2e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e298
          have b2e343 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X2 X1) (M.op (M.op (M.op y X1) X3) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e297 X0 X1 X2 X3
               have i₂ := b2e204 X0 X1 X2 (M.op (M.op y X1) X3)
               grind)
            | (have i₁ := b2e297 X3 X0 X1 X3
               have i₂ := b2e204 X0 X1 (M.op (M.op y X0) X3) X3
               grind)
            | exact superpose b2e204 b2e297
            | exact resolve b2e297 b2e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e297
          have b2e346 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 x) (M.op X1 x)) := by
            intro X0 X1
            first
            | (have i₁ := b2e291 X0 X1
               have i₂ := b2e247 X1 X0
               grind)
            | exact superpose b2e247 b2e291
            | exact resolve b2e291 b2e247
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e291
          have b2e350 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 x) X2)) = (M.op (M.op X1 y) (M.op (M.op x X0) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e284 X0 X1 X2
               have i₂ := b2e204 X2 y X1 (M.op x X0)
               grind)
            | (have i₁ := b2e284 X0 X1 x
               have i₂ := b2e204 y X1 (M.op x X0) x
               grind)
            | exact superpose b2e204 b2e284
            | exact resolve b2e284 b2e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e284
          have b2e352 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (σ y) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e281 X0 X1
               have i₂ := b2e13 X0 X1 (σ y)
               grind)
            | exact superpose b2e13 b2e281
            | exact resolve b2e281 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e281
          have b2e355 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 x) X1) (M.op X2 (M.op x X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e277 X0 X1 X2
               have i₂ := b2e96 X2 X1
               grind)
            | exact superpose b2e96 b2e277
            | exact resolve b2e277 b2e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e277
          have b2e362 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e332 X0 X1
               have i₂ := b2e168 X1 X0
               grind)
            | exact superpose b2e168 b2e332
            | exact resolve b2e332 b2e168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e332
          have b2e363 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 y)) = (M.op (M.op X0 y) (M.op X1 (M.op (M.op X0 y) X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e333 X0 X1 X2
               have i₂ := b2e204 X1 (M.op (M.op X0 y) X2) y X0
               grind)
            | (have i₁ := b2e333 X0 X1 X2
               have i₂ := b2e204 X0 X1 (M.op (M.op X0 y) X2) y
               grind)
            | exact superpose b2e204 b2e333
            | exact resolve b2e333 b2e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e333
          have b2e364 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 y)) = (M.op (M.op X0 x) (M.op X1 (M.op (M.op X0 x) X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e334 X0 X1 X2
               have i₂ := b2e204 X1 (M.op (M.op X0 x) X2) x X0
               grind)
            | (have i₁ := b2e334 X0 X1 X2
               have i₂ := b2e204 X0 X1 (M.op (M.op X0 x) X2) x
               grind)
            | exact superpose b2e204 b2e334
            | exact resolve b2e334 b2e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e334
          have b2e366 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x X0))) = (M.op (M.op X1 x) (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e339 X0 X1 X2
               have i₂ := b2e164 X2 X0
               grind)
            | (have i₁ := b2e339 X2 X1 X2
               have i₂ := b2e164 (M.op y X2) X2
               grind)
            | exact superpose b2e164 b2e339
            | exact resolve b2e339 b2e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e339
          have b2e368 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X2 X1) (M.op (M.op X1 X3) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e343 X0 X1 X2 X3
               have i₂ := b2e164 X1 X3
               grind)
            | (have i₁ := b2e343 X0 X1 X2 X2
               have i₂ := b2e164 (M.op y X1) X2
               grind)
            | exact superpose b2e164 b2e343
            | exact resolve b2e343 b2e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e343
          have b2e372 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 x) X2)) = (M.op X1 (M.op (M.op x X0) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e350 X0 X1 X2
               have i₂ := b2e117 X1 (M.op (M.op x X0) X2)
               grind)
            | exact superpose b2e117 b2e350
            | exact resolve b2e350 b2e117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e350
          have b2e376 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X0) (M.op (M.op (M.op X0 x) x) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e355 X0 X1 X2
               have i₂ := b2e315 X2 x X0 X1 (M.op X0 x)
               grind)
            | exact superpose b2e315 b2e355
            | exact resolve b2e355 b2e315
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e315 b2e355
          have b2e382 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 y)) = (M.op X0 (M.op X1 (M.op (M.op X0 y) X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e363 X0 X1 X2
               have i₂ := b2e117 X0 (M.op X1 (M.op (M.op X0 y) X2))
               grind)
            | exact superpose b2e117 b2e363
            | exact resolve b2e363 b2e117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e363
          have b2e383 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 x) (M.op X1 (M.op (M.op X0 x) X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e364 X0 X1 X2
               have i₂ := b2e168 X2 X1
               grind)
            | exact superpose b2e168 b2e364
            | exact resolve b2e364 b2e168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e364
          have b2e386 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 x) X2)) = (M.op X1 (M.op x (M.op X2 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e372 X0 X1 X2
               have i₂ := b2e270 X0 X2
               grind)
            | exact superpose b2e270 b2e372
            | exact resolve b2e372 b2e270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e270 b2e372
          have b2e389 : ∀ X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op x (M.op x X2))) := by
            intro X1 X2
            first
            | (have i₁ := b2e376 x X1 X2
               have i₂ := b2e342 X2 x X1 x x
               grind)
            | exact superpose b2e342 b2e376
            | exact resolve b2e376 b2e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e342 b2e376
          have b2e394 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 y)) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e382 X0 X1 X2
               have i₂ := b2e117 X0 X2
               grind)
            | exact superpose b2e117 b2e382
            | exact resolve b2e382 b2e117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e382
          have b2e395 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X1 (M.op x (M.op (M.op X0 x) X2)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e383 X0 X1 X2
               have i₂ := b2e366 (M.op (M.op X0 x) X2) X0 X1
               grind)
            | exact superpose b2e366 b2e383
            | exact resolve b2e383 b2e366
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e366 b2e383
          have b2e397 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e394 X0 X1 X2
               have i₂ := b2e168 X2 X1
               grind)
            | exact superpose b2e168 b2e394
            | exact resolve b2e394 b2e168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e394
          have b2e398 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X1 (M.op x (M.op x (M.op X2 X0))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e395 X0 X1 X2
               have i₂ := b2e386 X0 x X2
               grind)
            | exact superpose b2e386 b2e395
            | exact resolve b2e395 b2e386
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e386 b2e395
          have b2e399 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e398 X0 X1 X2
               have i₂ := b2e389 X1 (M.op X2 X0)
               grind)
            | (have i₁ := b2e398 X0 X1 X2
               have i₂ := b2e389 X1 (M.op x (M.op x (M.op X2 X0)))
               grind)
            | exact superpose b2e389 b2e398
            | exact resolve b2e398 b2e389
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e389 b2e398
          have b2e417 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (M.op X3 X1) X0)) = (M.op y (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e247 (M.op X2 X3) (M.op (M.op X3 X1) X0)
               have i₂ := b2e42 X2 X3 X0 X1
               grind)
            | exact superpose b2e42 b2e247
            | exact resolve b2e247 b2e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e422 : (σ y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b2e247 (σ y) (σ y)
               have i₂ := b2e125
               grind)
            | exact superpose b2e125 b2e247
            | exact resolve b2e247 b2e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e433 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b2e96 X0 y
               have i₂ := b2e247 X0 y
               grind)
            | exact superpose b2e247 b2e96
            | exact resolve b2e96 b2e247
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e434 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) y) = (M.op (M.op X0 X2) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e39 X0 X2 X1 y
               have i₂ := b2e247 X0 X1
               grind)
            | exact superpose b2e247 b2e39
            | exact resolve b2e39 b2e247
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e436 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op (M.op (M.op X1 X0) X2) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 X2 y (M.op X1 X0)
               have i₂ := b2e247 X0 X1
               grind)
            | exact superpose b2e247 b2e13
            | exact resolve b2e13 b2e247
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e447 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op (M.op X2 X1) (M.op (M.op X1 X0) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e436 X0 X1 X2
               have i₂ := b2e204 X0 X1 X2 (M.op X1 X0)
               grind)
            | (have i₁ := b2e436 x X0 X1
               have i₂ := b2e204 X0 X1 (M.op X0 x) x
               grind)
            | exact superpose b2e204 b2e436
            | exact resolve b2e436 b2e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e436
          have b2e449 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X0 X2) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e434 X0 X1 X2
               have i₂ := b2e222 X2 X1
               grind)
            | exact superpose b2e222 b2e434
            | exact resolve b2e434 b2e222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e222 b2e434
          have b2e456 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X2 X3) (M.op (M.op X3 X1) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e417 X0 X1 X2 X3
               have i₂ := b2e247 (M.op X1 X2) X0
               grind)
            | exact superpose b2e247 b2e417
            | exact resolve b2e417 b2e247
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e417
          have b2e463 : ∀ X0 X2 : G, (M.op X2 y) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X2
            first
            | (have i₁ := b2e447 X0 x X2
               have i₂ := b2e368 X0 x X2 X0
               grind)
            | exact superpose b2e368 b2e447
            | exact resolve b2e447 b2e368
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e447
          have b2e465 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X0)) = (M.op (M.op X1 X2) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e456 X0 X1 X2 x
               have i₂ := b2e368 X0 x X2 X1
               grind)
            | exact superpose b2e368 b2e456
            | exact resolve b2e456 b2e368
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e368 b2e456
          have b2e482 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op (σ y) (M.op X1 (M.op X0 y))) := by
            intro X0 X1
            first
            | (have i₁ := b2e39 y (σ y) X0 X1
               have i₂ := b2e422
               grind)
            | exact superpose b2e422 b2e39
            | exact resolve b2e39 b2e422
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e491 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op (σ y) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e482 X0 X1
               have i₂ := b2e168 X0 X1
               grind)
            | exact superpose b2e168 b2e482
            | exact resolve b2e482 b2e168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e482
          have b2e494 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (σ y) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e491 X0 X1
               have i₂ := b2e465 X1 (σ y) X0
               grind)
            | (have i₁ := b2e491 X0 (M.op X1 X0)
               have i₂ := b2e465 X0 X1 (M.op (σ y) X0)
               grind)
            | exact superpose b2e465 b2e491
            | exact resolve b2e491 b2e465
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e491
          have b2e497 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ y) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e494 X0 X1
               have i₂ := b2e352 X0 X1
               grind)
            | exact superpose b2e352 b2e494
            | exact resolve b2e494 b2e352
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e352 b2e494
          have b2e539 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (σ x) (M.op X1 X0)) ∨ (M.op (σ x) X1) = (k X1 (σ x)) ∨ (σ x) = (M.op X1 (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b2e38 (M.op X1 X0)
               have i₂ := b2e67 (σ x) X0 X1
               grind)
            | exact superpose b2e67 b2e38
            | (have j1 := b2e67 (σ x) X1 X1
               grind)
            | exact resolve b2e38 b2e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e67
          have b2e543 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ x) (M.op X1 X0)) ∨ (M.op (σ x) X1) = (k X1 (σ x)) ∨ (σ x) = (M.op X1 (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b2e539 X0 X1
               have i₂ := b2e497 X1 X0
               grind)
            | exact superpose b2e497 b2e539
            | (have j0 := b2e539 X0 X1
               grind)
            | exact resolve b2e539 b2e497
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e539
          have b2e872 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 (M.op y X1)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e39 (M.op y X1) X0 X2 X3
               have i₂ := b2e362 X0 X1
               grind)
            | exact superpose b2e362 b2e39
            | exact resolve b2e39 b2e362
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e39
          have b2e882 : ∀ X0 : G, (M.op (σ x) (M.op y X0)) = (M.op (σ y) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b2e38 (M.op y X0)
               have i₂ := b2e362 (σ x) X0
               grind)
            | exact superpose b2e362 b2e38
            | exact resolve b2e38 b2e362
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e38 b2e362
          have b2e886 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (σ x) (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b2e882 X0
               have i₂ := b2e497 X0 (σ x)
               grind)
            | exact superpose b2e497 b2e882
            | exact resolve b2e882 b2e497
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e497 b2e882
          have b2e896 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X1 (M.op X0 (M.op X3 (M.op X2 (M.op y X1))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e872 X0 X1 X2 X3
               have i₂ := b2e465 (M.op X3 (M.op X2 (M.op y X1))) X0 X1
               grind)
            | (have i₁ := b2e872 X0 X1 X2 X1
               have i₂ := b2e465 (M.op X2 (M.op y X1)) X1 (M.op X0 X1)
               grind)
            | exact superpose b2e465 b2e872
            | exact resolve b2e872 b2e465
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e872
          have b2e913 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b2e886 X0
               have i₂ := b2e96 X0 (σ x)
               grind)
            | exact superpose b2e96 b2e886
            | exact resolve b2e886 b2e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e886
          have b2e921 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X1 (M.op X0 (M.op X3 (M.op X2 X1)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e896 X0 X1 X2 X3
               have i₂ := b2e96 X1 X2
               grind)
            | exact superpose b2e96 b2e896
            | exact resolve b2e896 b2e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e96 b2e896
          have b2e935 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op X1 (M.op X0 (M.op X3 (M.op X2 X1)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e921 X0 X1 X2 X3
               have i₂ := b2e465 X3 X0 X2
               grind)
            | (have i₁ := b2e921 X0 X1 X2 (M.op X1 X0)
               have i₂ := b2e465 X0 X1 (M.op X0 X2)
               grind)
            | exact superpose b2e465 b2e921
            | exact resolve b2e921 b2e465
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e921
          have b2e961 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X1))) X2) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 X1)))) ∨ (M.op X0 (M.op X1 (M.op X0 X1))) = X2 ∨ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e69 X0 (M.op (M.op X1 x) X1)
               have i₂ := b2e42 (M.op X1 x) X1 X1 x
               grind)
            | exact superpose b2e42 b2e69
            | exact resolve b2e69 b2e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e69
          have b2e974 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (k (M.op X1 X1) X2) ∨ (M.op X0 (M.op X1 (M.op X0 X1))) = X2 ∨ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e961 X0 X2 X2
               have i₂ := b2e397 X0 X2 X2
               grind)
            | exact superpose b2e397 b2e961
            | (have j0 := b2e961 X0 X1 X2
               grind)
            | exact resolve b2e961 b2e397
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e961
          have b2e981 : ∀ X0 X1 X2 : G, (M.op X2 y) = (k (M.op X1 X1) X2) ∨ (M.op X0 (M.op X1 (M.op X0 X1))) = X2 ∨ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e974 X0 X1 X2
               have i₂ := b2e463 X1 X2
               grind)
            | exact superpose b2e463 b2e974
            | (have j0 := b2e974 X0 X1 X2
               grind)
            | exact resolve b2e974 b2e463
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e974
          have b2e987 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X2 ∨ (M.op X2 y) = (k (M.op X1 X1) X2) ∨ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e981 X0 X1 X2
               have i₂ := b2e397 X0 X1 X1
               grind)
            | exact superpose b2e397 b2e981
            | (have j0 := b2e981 X0 X1 X2
               grind)
            | exact resolve b2e981 b2e397
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e397 b2e981
          have b2e991 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X0 X2)) = X2 ∨ (M.op X1 X1) = X2 ∨ (M.op X2 y) = (k (M.op X1 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e987 X0 X1 X2
               have i₂ := b2e465 X2 X0 (M.op X1 (M.op X0 X1))
               grind)
            | (have i₁ := b2e987 X0 X1 (M.op X1 X0)
               have i₂ := b2e465 X0 X1 (M.op X0 (M.op X1 (M.op X0 X1)))
               grind)
            | exact superpose b2e465 b2e987
            | (have j0 := b2e987 X0 X1 X2
               grind)
            | exact resolve b2e987 b2e465
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e987
          have b2e995 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1))) = X2 ∨ (M.op X1 X1) = X2 ∨ (M.op X2 y) = (k (M.op X1 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e991 X0 X1 X2
               have i₂ := b2e204 X2 (M.op X0 X1) X1 X0
               grind)
            | (have i₁ := b2e991 X0 x X1
               have i₂ := b2e204 X0 X1 (M.op X0 x) x
               grind)
            | exact superpose b2e204 b2e991
            | (have j0 := b2e991 X0 X1 X2
               grind)
            | exact resolve b2e991 b2e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e204 b2e991
          have b2e999 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X1)))) = X2 ∨ (M.op X1 X1) = X2 ∨ (M.op X2 y) = (k (M.op X1 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e995 X0 X1 X2
               have i₂ := b2e465 (M.op X2 (M.op X0 X1)) X0 X1
               grind)
            | (have i₁ := b2e995 X0 X1 X1
               have i₂ := b2e465 (M.op X0 X1) X1 (M.op X0 X1)
               grind)
            | exact superpose b2e465 b2e995
            | (have j0 := b2e995 X0 X1 X2
               grind)
            | exact resolve b2e995 b2e465
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e995
          have b2e1003 : ∀ X0 X1 X2 : G, (M.op X2 y) = (k (M.op X1 X1) X2) ∨ (M.op X0 (M.op X0 X2)) = X2 ∨ (M.op X1 X1) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e999 X0 X1 X2
               have i₂ := b2e935 X0 X1 X0 X2
               grind)
            | exact superpose b2e935 b2e999
            | (have j0 := b2e999 X0 X1 X2
               grind)
            | exact resolve b2e999 b2e935
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e935 b2e999
          have b2e1032 : ∀ X0 : G, (M.op X0 x) = (M.op y (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b2e433 (M.op X0 x)
               have i₂ := b2e98 X0
               grind)
            | exact superpose b2e98 b2e433
            | exact resolve b2e433 b2e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e98
          have b2e1049 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b2e1032 X0
               have i₂ := b2e247 x X0
               grind)
            | exact superpose b2e247 b2e1032
            | exact resolve b2e1032 b2e247
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1032
          have b2e1143 : ∀ X0 X1 X2 : G, (M.op X1 (σ X2)) = (M.op (M.op (σ X0) X1) (σ X0)) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 X1 (σ X2) (σ X0)
               have i₂ := b2e62 X0 X2
               grind)
            | exact superpose b2e62 b2e13
            | (have j1 := b2e62 X0 X2
               grind)
            | exact resolve b2e13 b2e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e62
          have b2e1176 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 (σ X2)) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e1143 X0 X1 X2
               have i₂ := b2e157 (σ X0) X1
               grind)
            | exact superpose b2e157 b2e1143
            | (have j0 := b2e1143 X0 X1 X2
               grind)
            | exact resolve b2e1143 b2e157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1143
          have b2e1957 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b2e463 (σ y) X0
               have i₂ := b2e125
               grind)
            | exact superpose b2e125 b2e463
            | exact resolve b2e463 b2e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e2004 : ∀ X0 : G, (M.op X0 X0) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b2e247 X0 X0
               have i₂ := b2e463 X0 y
               grind)
            | exact superpose b2e463 b2e247
            | exact resolve b2e247 b2e463
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e247 b2e463
          have b2e2014 : ∀ X0 : G, (M.op X0 X0) = y := by
            intro X0
            first
            | (have i₁ := b2e2004 X0
               have i₂ := b2e44
               grind)
            | exact superpose b2e44 b2e2004
            | exact resolve b2e2004 b2e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2004
          have b2e2257 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op x X0) (M.op x X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X1 X0 x
               have i₂ := b2e335 (M.op x X1) X0
               grind)
            | (have i₁ := b2e13 X1 X1 x
               have i₂ := b2e335 (M.op X1 x) X1
               grind)
            | exact superpose b2e335 b2e13
            | exact resolve b2e13 b2e335
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e335
          have b2e2334 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e2257 X1 X0
               have i₂ := b2e449 x X0 X1
               grind)
            | exact superpose b2e449 b2e2257
            | exact resolve b2e2257 b2e449
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e449 b2e2257
          have b2e2593 : y = (σ y) := by
            first
            | (have i₁ := b2e125
               have i₂ := b2e2014 (σ y)
               grind)
            | exact superpose b2e2014 b2e125
            | exact resolve b2e125 b2e2014
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e125
          have b2e2812 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e2593
               grind)
            | exact superpose b2e2593 b2e20
            | exact resolve b2e20 b2e2593
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e2813 : y = (τ y) := by
            first
            | (have i₁ := b2e14 y
               have i₂ := b2e2593
               grind)
            | exact superpose b2e2593 b2e14
            | exact resolve b2e14 b2e2593
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e2814 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b2e19 y X0
               have i₂ := b2e2593
               grind)
            | exact superpose b2e2593 b2e19
            | exact resolve b2e19 b2e2593
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e2822 : ∀ X0 : G, (k y (τ X0)) = (τ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b2e87 y X0
               have i₂ := b2e2593
               grind)
            | exact superpose b2e2593 b2e87
            | exact resolve b2e87 b2e2593
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e2828 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b2e2812
               have i₂ := b2e913 y
               grind)
            | exact superpose b2e913 b2e2812
            | exact resolve b2e2812 b2e913
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2812
          have b2e3118 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op (M.op X3 X1) X0) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e399 X3 (M.op (M.op X3 X1) X0) X2
               have i₂ := b2e42 X2 X3 X0 X1
               grind)
            | exact superpose b2e42 b2e399
            | exact resolve b2e399 b2e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e42 b2e399
          have b2e3205 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X0 (M.op (M.op X3 X1) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e3118 X0 X1 X2 X3
               have i₂ := b2e465 X2 (M.op X3 X1) X0
               grind)
            | (have i₁ := b2e3118 X0 X1 (M.op X1 X0) X3
               have i₂ := b2e465 X0 X1 (M.op (M.op X3 X1) X0)
               grind)
            | exact superpose b2e465 b2e3118
            | exact resolve b2e3118 b2e465
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e3118
          have b2e3259 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X0 (M.op X1 (M.op X3 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e3205 X0 X1 X2 X3
               have i₂ := b2e465 X2 X3 X1
               grind)
            | (have i₁ := b2e3205 X0 X1 (M.op X1 X0) X3
               have i₂ := b2e465 X0 X1 (M.op X3 X1)
               grind)
            | exact superpose b2e465 b2e3205
            | exact resolve b2e3205 b2e465
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e465 b2e3205
          have b2e3806 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e17 X1 X0
               have i₂ := b2e2334 X1 X0
               grind)
            | (have i₁ := b2e17 X1 X0
               have i₂ := b2e2334 X0 X1
               grind)
            | exact superpose b2e2334 b2e17
            | (have j0 := b2e17 X1 X0
               grind)
            | exact resolve b2e17 b2e2334
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e3886 : ∀ X0 X1 : G, y = X0 ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e3806 X0 X1
               have i₂ := b2e2014 X1
               grind)
            | exact superpose b2e2014 b2e3806
            | (have j0 := b2e3806 X0 X1
               grind)
            | (have r₁ := b2e3806 y y
               have r₂ := b2e2014 y
               grind)
            | exact resolve b2e3806 b2e2014
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e3806
          have b2e3949 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ y = X0 ∨ y = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e3886 X0 X1
               have i₂ := b2e2014 X0
               grind)
            | exact superpose b2e2014 b2e3886
            | (have j0 := b2e3886 X0 X1
               grind)
            | (have r₁ := b2e3886 y y
               have r₂ := b2e2014 y
               grind)
            | exact resolve b2e3886 b2e2014
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e3886
          have b2e110985 : ∀ X0 X1 : G, x = (M.op (M.op X0 x) X0) ∨ (M.op x y) = (k (M.op X1 X1) x) ∨ (M.op X1 X1) = x := by
            intro X0 X1
            first
            | (have i₁ := b2e346 X0 (M.op X0 x)
               have i₂ := b2e1003 (M.op X0 x) X1 x
               grind)
            | exact superpose b2e1003 b2e346
            | (have j1 := b2e1003 X0 X1 x
               grind)
            | exact resolve b2e346 b2e1003
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e346 b2e1003
          have b2e111098 : ∀ X1 : G, x = (M.op x y) ∨ (M.op x y) = (k (M.op X1 X1) x) ∨ (M.op X1 X1) = x := by
            intro X1
            first
            | (have i₁ := b2e110985 x X1
               have i₂ := b2e157 x x
               grind)
            | exact superpose b2e157 b2e110985
            | (have j0 := b2e110985 x X1
               grind)
            | exact resolve b2e110985 b2e157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e157 b2e110985
          have b2e111481 : ∀ X1 : G, (M.op x y) = (k (M.op X1 X1) x) ∨ (M.op X1 X1) = x := by
            intro X1
            first
            | (have j0 := b2e111098 X1
               grind)
            | (have r₁ := b2e111098 X1
               have r₂ := b2e256
               grind)
            | exact resolve b2e111098 b2e256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e256 b2e111098
          have b2e111763 : ∀ X1 : G, (M.op x y) = (k y x) ∨ (M.op X1 X1) = x := by
            intro X1
            first
            | (have i₁ := b2e111481 X1
               have i₂ := b2e2014 X1
               grind)
            | exact superpose b2e2014 b2e111481
            | (have j0 := b2e111481 X1
               grind)
            | exact resolve b2e111481 b2e2014
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e111481
          have b2e111971 : x = y ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b2e111763 x
               have i₂ := b2e2014 x
               grind)
            | exact superpose b2e2014 b2e111763
            | exact resolve b2e111763 b2e2014
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e111763
          have b2e112108 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b2e111971
               have r₂ := b2e53
               grind)
            | exact resolve b2e111971 b2e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e111971
          have b2e112455 : (k y (τ x)) = (τ (M.op x y)) := by
            first
            | (have i₁ := b2e2822 x
               have i₂ := b2e112108
               grind)
            | exact superpose b2e112108 b2e2822
            | exact resolve b2e2822 b2e112108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e113548 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e63 X0 (σ X0)
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e63
            | exact resolve b2e63 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e63
          have b2e113755 : ∀ X0 X1 : G, y = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e113548 X0 X1
               have i₂ := b2e2014 X0
               grind)
            | exact superpose b2e2014 b2e113548
            | (have j0 := b2e113548 X0 X1
               grind)
            | exact resolve b2e113548 b2e2014
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e113548
          have b2e113835 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ y = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e113755 X0 X1
               have i₂ := b2e19 X0 X1
               grind)
            | exact superpose b2e19 b2e113755
            | (have j0 := b2e113755 X0 X1
               grind)
            | exact resolve b2e113755 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e113755
          have b2e188093 : (M.op (σ x) y) = (M.op (σ x) (M.op (σ x) y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b2e543 (σ x) (σ y)
               have i₂ := b2e158
               grind)
            | exact superpose b2e158 b2e543
            | (have j0 := b2e543 y (σ x)
               grind)
            | exact resolve b2e543 b2e158
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e158 b2e543
          have b2e188406 : (M.op (σ x) (σ x)) = (M.op (σ x) y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b2e188093
               have i₂ := b2e168 (σ x) (σ x)
               grind)
            | exact superpose b2e168 b2e188093
            | exact resolve b2e188093 b2e168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e188093
          have b2e188445 : (M.op (σ x) (σ x)) = (M.op y (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b2e188406
               have i₂ := b2e913 y
               grind)
            | exact superpose b2e913 b2e188406
            | exact resolve b2e188406 b2e913
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e188406
          have b2e188472 : (σ y) = (M.op y (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b2e188445
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e188445
            | exact resolve b2e188445 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e188445
          have b2e188487 : y = (M.op y (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b2e188472
               have i₂ := b2e2593
               grind)
            | exact superpose b2e2593 b2e188472
            | exact resolve b2e188472 b2e2593
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e188472
          have b2e188496 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op y (σ x)) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b2e188487
               have i₂ := b2e19 y x
               grind)
            | exact superpose b2e19 b2e188487
            | exact resolve b2e188487 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e188487
          have b2e188501 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y (σ x)) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b2e188496
               have i₂ := b2e112108
               grind)
            | exact superpose b2e112108 b2e188496
            | exact resolve b2e188496 b2e112108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e188496
          have b2e188503 : y = (M.op y (σ x)) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have r₁ := b2e188501
               have r₂ := b2e20
               grind)
            | exact resolve b2e188501 b2e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e188501
          have b2e188504 : (σ x) = (M.op y (σ x)) ∨ y = (M.op y (σ x)) := by
            first
            | (have i₁ := b2e188503
               have i₂ := b2e913 y
               grind)
            | exact superpose b2e913 b2e188503
            | exact resolve b2e188503 b2e913
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e188503
          have b2e191259 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op (σ y) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e135 (σ y)
               have i₂ := b2e18 (σ y) x
               grind)
            | (have i₁ := b2e135 X0
               have i₂ := b2e18 X0 (M.op X0 (σ y))
               grind)
            | exact superpose b2e18 b2e135
            | (have j1 := b2e18 (σ y) X0
               grind)
            | exact resolve b2e135 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e135
          have b2e191473 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b2e191259 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e191259
          have b2e191631 : ∀ X0 : G, (M.op y X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b2e191473 X0
               have i₂ := b2e2593
               grind)
            | exact superpose b2e2593 b2e191473
            | (have j0 := b2e191473 X0
               grind)
            | exact resolve b2e191473 b2e2593
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e191473
          have b2e191740 : ∀ X0 : G, (M.op X0 y) = (k (σ y) X0) ∨ (M.op y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e191631 X0
               have i₂ := b2e1957 X0
               grind)
            | exact superpose b2e1957 b2e191631
            | (have j0 := b2e191631 X0
               grind)
            | exact resolve b2e191631 b2e1957
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1957 b2e191631
          have b2e191819 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ (M.op y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e191740 X0
               have i₂ := b2e2593
               grind)
            | exact superpose b2e2593 b2e191740
            | (have j0 := b2e191740 X0
               grind)
            | exact resolve b2e191740 b2e2593
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e191740
          have b2e194953 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X1)) = X0 ∨ (M.op X2 y) = (M.op X2 (σ X1)) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e1176 (τ X0) X1 X2
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e1176
            | (have j0 := b2e1176 X0 X2 X1
               grind)
            | exact resolve b2e1176 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1176
          have b2e195886 : ∀ X0 X1 X2 : G, y = X0 ∨ (M.op X2 y) = (M.op X2 (σ X1)) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e194953 X0 X1 X2
               have i₂ := b2e2014 (σ X1)
               grind)
            | exact superpose b2e2014 b2e194953
            | (have j0 := b2e194953 X0 X1 X2
               grind)
            | exact resolve b2e194953 b2e2014
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2014 b2e194953
          have b2e196085 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X2 y) = (M.op X2 (σ X1)) ∨ y = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e195886 X0 X1 X2
               have i₂ := b2e30 X0 X1
               grind)
            | exact superpose b2e30 b2e195886
            | (have j0 := b2e195886 X0 X1 X2
               grind)
            | exact resolve b2e195886 b2e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e195886
          have b2e196821 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op X0 y)) ∨ (M.op y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e2822 X0
               have i₂ := b2e191819 X0
               grind)
            | exact superpose b2e191819 b2e2822
            | (have j1 := b2e191819 X0
               grind)
            | exact resolve b2e2822 b2e191819
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2822
          have b2e257922 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ y = X1 ∨ (k X0 X1) = y := by
            intro X0 X1
            first
            | (have i₁ := b2e3949 X1 X0
               have i₂ := b2e2334 X1 X0
               grind)
            | (have i₁ := b2e3949 X1 X0
               have i₂ := b2e2334 X0 X1
               grind)
            | exact superpose b2e2334 b2e3949
            | (have j0 := b2e3949 X1 X0
               grind)
            | exact resolve b2e3949 b2e2334
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2334 b2e3949
          have b2e271357 : (σ x) ≠ (σ x) ∨ y = (σ x) ∨ y = (k y (σ x)) ∨ y = (M.op y (σ x)) := by
            first
            | (have i₁ := b2e257922 y (σ x)
               have i₂ := b2e188504
               grind)
            | exact superpose b2e188504 b2e257922
            | (have j0 := b2e257922 y (σ x)
               grind)
            | (have r₁ := b2e257922 y (σ x)
               have r₂ := b2e188504
               grind)
            | exact resolve b2e257922 b2e188504
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e271358 : y ≠ (σ x) ∨ y = (M.op y (σ x)) := by grind
          have b2e271359 : y = (σ x) ∨ y = (k y (σ x)) ∨ y = (M.op y (σ x)) := by grind
          clear b2e271357
          have b2e271362 : y = (k y (σ x)) ∨ y = (M.op y (σ x)) := by
            first
            | (have r₁ := b2e271359
               have r₂ := b2e271358
               grind)
            | exact resolve b2e271359 b2e271358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e271358 b2e271359
          have b2e271422 : y = (σ (k y x)) ∨ y = (M.op y (σ x)) := by
            first
            | (have i₁ := b2e271362
               have i₂ := b2e2814 x
               grind)
            | exact superpose b2e2814 b2e271362
            | exact resolve b2e271362 b2e2814
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e271362
          have b2e271466 : y = (σ (M.op x y)) ∨ y = (M.op y (σ x)) := by
            first
            | (have i₁ := b2e271422
               have i₂ := b2e112108
               grind)
            | exact superpose b2e112108 b2e271422
            | exact resolve b2e271422 b2e112108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e271422
          have b2e272803 : (M.op x y) = (τ y) ∨ y = (M.op y (σ x)) := by
            first
            | (have i₁ := b2e14 (M.op x y)
               have i₂ := b2e271466
               grind)
            | exact superpose b2e271466 b2e14
            | exact resolve b2e14 b2e271466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e271466
          have b2e272849 : y = (M.op y (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e272803
               have i₂ := b2e2813
               grind)
            | exact superpose b2e2813 b2e272803
            | exact resolve b2e272803 b2e2813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e272803
          have b2e274011 : y = (k y (M.op y (σ x))) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e153 (σ x)
               have i₂ := b2e272849
               grind)
            | exact superpose b2e272849 b2e153
            | exact resolve b2e153 b2e272849
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e153
          have b2e274015 : ∀ X0 : G, (M.op (σ x) X0) = (M.op y X0) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b2e164 (σ x) X0
               have i₂ := b2e272849
               grind)
            | exact superpose b2e272849 b2e164
            | exact resolve b2e164 b2e272849
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e164 b2e272849
          have b2e314532 : (σ (M.op x y)) ≠ (M.op y (σ y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e274015 (σ y)
               grind)
            | exact superpose b2e274015 b2e20
            | exact resolve b2e20 b2e274015
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e314949 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e314532
               have i₂ := b2e422
               grind)
            | exact superpose b2e422 b2e314532
            | exact resolve b2e314532 b2e422
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e422 b2e314532
          have b2e315129 : y ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e314949
               have i₂ := b2e2593
               grind)
            | exact superpose b2e2593 b2e314949
            | exact resolve b2e314949 b2e2593
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e314949
          have b2e588459 : (τ (M.op y y)) = (k y (τ (σ x))) ∨ (σ x) = (M.op y (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e196821 (σ x)
               have i₂ := b2e274015 y
               grind)
            | exact superpose b2e274015 b2e196821
            | (have j0 := b2e196821 (σ x)
               grind)
            | exact resolve b2e196821 b2e274015
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e196821 b2e274015
          have b2e588486 : (k y x) = (τ (M.op y y)) ∨ (σ x) = (M.op y (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e588459
               have i₂ := b2e14 x
               grind)
            | exact superpose b2e14 b2e588459
            | exact resolve b2e588459 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e588459
          have b2e588491 : (k y x) = (τ y) ∨ (σ x) = (M.op y (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e588486
               have i₂ := b2e44
               grind)
            | exact superpose b2e44 b2e588486
            | exact resolve b2e588486 b2e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e44 b2e588486
          have b2e588494 : y = (k y x) ∨ (σ x) = (M.op y (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e588491
               have i₂ := b2e2813
               grind)
            | exact superpose b2e2813 b2e588491
            | exact resolve b2e588491 b2e2813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e588491
          have b2e588496 : y = (M.op x y) ∨ (σ x) = (M.op y (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e588494
               have i₂ := b2e112108
               grind)
            | exact superpose b2e112108 b2e588494
            | exact resolve b2e588494 b2e112108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e588494
          have b2e588497 : (σ x) = (M.op y (σ x)) ∨ y = (M.op x y) := by grind
          clear b2e588496
          have b2e590655 : y = (k y (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e274011
               have i₂ := b2e588497
               grind)
            | exact superpose b2e588497 b2e274011
            | exact resolve b2e274011 b2e588497
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e274011 b2e588497
          have b2e590773 : y = (k y (σ x)) ∨ y = (M.op x y) := by grind
          clear b2e590655
          have b2e590836 : y = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e590773
               have i₂ := b2e2814 x
               grind)
            | exact superpose b2e2814 b2e590773
            | exact resolve b2e590773 b2e2814
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2814 b2e590773
          have b2e590862 : y = (σ (M.op x y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e590836
               have i₂ := b2e112108
               grind)
            | exact superpose b2e112108 b2e590836
            | exact resolve b2e590836 b2e112108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e112108 b2e590836
          have b2e590869 : y = (M.op x y) := by
            first
            | (have r₁ := b2e590862
               have r₂ := b2e315129
               grind)
            | exact resolve b2e590862 b2e315129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e315129 b2e590862
          have b2e593417 : (σ y) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b2e2828
               have i₂ := b2e590869
               grind)
            | exact superpose b2e590869 b2e2828
            | exact resolve b2e2828 b2e590869
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e593419 : (τ y) = (k y (τ x)) := by
            first
            | (have i₁ := b2e112455
               have i₂ := b2e590869
               grind)
            | exact superpose b2e590869 b2e112455
            | exact resolve b2e112455 b2e590869
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e112455
          have b2e593468 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b2e117 x X0
               have i₂ := b2e590869
               grind)
            | exact superpose b2e590869 b2e117
            | exact resolve b2e117 b2e590869
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e117
          have b2e593469 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b2e168 x X0
               have i₂ := b2e590869
               grind)
            | exact superpose b2e590869 b2e168
            | exact resolve b2e168 b2e590869
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e593575 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op x (M.op X0 (M.op X1 y))) := by
            intro X0 X1
            first
            | (have i₁ := b2e3259 X0 X1 y x
               have i₂ := b2e590869
               grind)
            | exact superpose b2e590869 b2e3259
            | exact resolve b2e3259 b2e590869
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e3259 b2e590869
          have b2e593729 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e593575 X1 X0
               have i₂ := b2e168 X0 X1
               grind)
            | exact superpose b2e168 b2e593575
            | exact resolve b2e593575 b2e168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e168 b2e593575
          have b2e593850 : y = (k y (τ x)) := by
            first
            | (have i₁ := b2e593419
               have i₂ := b2e2813
               grind)
            | exact superpose b2e2813 b2e593419
            | exact resolve b2e593419 b2e2813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2813 b2e593419
          have b2e593851 : (σ y) ≠ (M.op x (σ x)) := by
            first
            | (have i₁ := b2e593417
               have i₂ := b2e593468 (σ x)
               grind)
            | exact superpose b2e593468 b2e593417
            | exact resolve b2e593417 b2e593468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e593417
          have b2e593993 : y ≠ (M.op x (σ x)) := by
            first
            | (have i₁ := b2e593851
               have i₂ := b2e2593
               grind)
            | exact superpose b2e2593 b2e593851
            | exact resolve b2e593851 b2e2593
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e593851
          have b2e601714 : y = (M.op (τ x) y) ∨ (τ x) = (M.op y (τ x)) := by
            first
            | (have i₁ := b2e191819 (τ x)
               have i₂ := b2e593850
               grind)
            | exact superpose b2e593850 b2e191819
            | (have j0 := b2e191819 (τ x)
               grind)
            | exact resolve b2e191819 b2e593850
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e191819 b2e593850
          have b2e601737 : y = (M.op y (τ x)) ∨ (τ x) = (M.op y (τ x)) := by
            first
            | (have i₁ := b2e601714
               have i₂ := b2e433 (τ x)
               grind)
            | exact superpose b2e433 b2e601714
            | exact resolve b2e601714 b2e433
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e433 b2e601714
          have b2e601766 : y = (M.op x (τ x)) ∨ (τ x) = (M.op y (τ x)) := by
            first
            | (have i₁ := b2e601737
               have i₂ := b2e593468 (τ x)
               grind)
            | exact superpose b2e593468 b2e601737
            | exact resolve b2e601737 b2e593468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e601737
          have b2e601791 : (τ x) = (M.op x (τ x)) ∨ y = (M.op x (τ x)) := by
            first
            | (have i₁ := b2e601766
               have i₂ := b2e593468 (τ x)
               grind)
            | exact superpose b2e593468 b2e601766
            | exact resolve b2e601766 b2e593468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e601766
          have b2e609108 : (σ x) = (M.op x (σ x)) ∨ y = (M.op x (σ x)) := by
            first
            | (have i₁ := b2e188504
               have i₂ := b2e593468 (σ x)
               grind)
            | exact superpose b2e593468 b2e188504
            | exact resolve b2e188504 b2e593468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e188504
          have b2e610283 : (σ x) = (M.op x (σ x)) := by
            first
            | (have r₁ := b2e609108
               have r₂ := b2e593993
               grind)
            | exact resolve b2e609108 b2e593993
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e609108
          have b2e616257 : (M.op y (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b2e2828
               have i₂ := b2e593469 x
               grind)
            | exact superpose b2e593469 b2e2828
            | exact resolve b2e2828 b2e593469
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2828 b2e593469
          have b2e616388 : (σ y) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b2e616257
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e616257
            | exact resolve b2e616257 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e616257
          have b2e616691 : (σ y) ≠ (M.op x (σ x)) := by
            first
            | (have i₁ := b2e616388
               have i₂ := b2e593468 (σ x)
               grind)
            | exact superpose b2e593468 b2e616388
            | exact resolve b2e616388 b2e593468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e616388
          have b2e616920 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b2e616691
               have i₂ := b2e610283
               grind)
            | exact superpose b2e610283 b2e616691
            | exact resolve b2e616691 b2e610283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e616691
          have b2e617069 : y ≠ (σ x) := by
            first
            | (have i₁ := b2e616920
               have i₂ := b2e2593
               grind)
            | exact superpose b2e2593 b2e616920
            | exact resolve b2e616920 b2e2593
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e616920
          have b2e687973 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = y ∨ y = (k x (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e257922 x (M.op X0 X1)
               have i₂ := b2e593729 X0 X1
               grind)
            | exact superpose b2e593729 b2e257922
            | (have j0 := b2e257922 x (M.op X0 X1)
               grind)
            | (have r₁ := b2e257922 x (M.op X0 X1)
               have r₂ := b2e593729 X0 X1
               grind)
            | exact resolve b2e257922 b2e593729
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e257922 b2e593729
          have b2e687980 : ∀ X0 X1 : G, y = (k x (M.op X0 X1)) ∨ (M.op X0 X1) = y := by
            intro X0 X1
            first
            | (have j0 := b2e687973 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e687973
          have b2e843387 : y = (k x (τ x)) ∨ y = (τ x) ∨ y = (M.op x (τ x)) := by
            first
            | (have i₁ := b2e687980 x (τ x)
               have i₂ := b2e601791
               grind)
            | exact superpose b2e601791 b2e687980
            | (have j0 := b2e687980 x (τ x)
               grind)
            | exact resolve b2e687980 b2e601791
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e687980
          have b2e843388 : y ≠ (τ x) ∨ y = (M.op x (τ x)) := by grind
          clear b2e601791
          have b2e843391 : y = (k x (τ x)) ∨ y = (M.op x (τ x)) := by
            first
            | (have r₁ := b2e843387
               have r₂ := b2e843388
               grind)
            | exact resolve b2e843387 b2e843388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e843387 b2e843388
          have b2e855216 : (σ y) = (k (σ x) x) ∨ y = (M.op x (τ x)) := by
            first
            | (have i₁ := b2e30 x x
               have i₂ := b2e843391
               grind)
            | exact superpose b2e843391 b2e30
            | exact resolve b2e30 b2e843391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e30 b2e843391
          have b2e855224 : y = (k (σ x) x) ∨ y = (M.op x (τ x)) := by
            first
            | (have i₁ := b2e855216
               have i₂ := b2e2593
               grind)
            | exact superpose b2e2593 b2e855216
            | exact resolve b2e855216 b2e2593
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e855216
          have b2e1025148 : ∀ X0 : G, (σ y) = (M.op (σ x) y) ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b2e22
               have i₂ := b2e196085 X0 x (σ x)
               grind)
            | exact superpose b2e196085 b2e22
            | (have j1 := b2e196085 X0 x x
               grind)
            | exact resolve b2e22 b2e196085
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e196085
          have b2e1025151 : ∀ X0 : G, (σ y) = (M.op y (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b2e1025148 X0
               have i₂ := b2e913 y
               grind)
            | exact superpose b2e913 b2e1025148
            | (have j0 := b2e1025148 X0
               grind)
            | exact resolve b2e1025148 b2e913
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e913 b2e1025148
          have b2e1025166 : ∀ X0 : G, (σ y) = (M.op x (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b2e1025151 X0
               have i₂ := b2e593468 (σ x)
               grind)
            | exact superpose b2e593468 b2e1025151
            | (have j0 := b2e1025151 X0
               grind)
            | exact resolve b2e1025151 b2e593468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e593468 b2e1025151
          have b2e1025170 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b2e1025166 X0
               have i₂ := b2e610283
               grind)
            | exact superpose b2e610283 b2e1025166
            | (have j0 := b2e1025166 X0
               grind)
            | exact resolve b2e1025166 b2e610283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1025166
          have b2e1025172 : ∀ X0 : G, y = (σ x) ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b2e1025170 X0
               have i₂ := b2e2593
               grind)
            | exact superpose b2e2593 b2e1025170
            | (have j0 := b2e1025170 X0
               grind)
            | exact resolve b2e1025170 b2e2593
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1025170
          have b2e1025174 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) ∨ y = X0 := by
            intro X0
            first
            | (have j0 := b2e1025172 X0
               grind)
            | (have r₁ := b2e1025172 X0
               have r₂ := b2e617069
               grind)
            | (have r₁ := b2e1025172 (σ x)
               have r₂ := b2e617069
               grind)
            | exact resolve b2e1025172 b2e617069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1025172
          have b2e1025226 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op X0 (σ x))) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b2e87 x X0
               have i₂ := b2e1025174 X0
               grind)
            | exact superpose b2e1025174 b2e87
            | (have j1 := b2e1025174 X0
               grind)
            | exact resolve b2e87 b2e1025174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e87
          have b2e1025241 : y = (M.op x (σ x)) ∨ y = (M.op x (τ x)) ∨ x = y := by
            first
            | (have i₁ := b2e855224
               have i₂ := b2e1025174 x
               grind)
            | exact superpose b2e1025174 b2e855224
            | (have j1 := b2e1025174 (M.op x (σ x))
               grind)
            | exact resolve b2e855224 b2e1025174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e855224 b2e1025174
          have b2e1025554 : y = (M.op x (τ x)) ∨ x = y := by
            first
            | (have r₁ := b2e1025241
               have r₂ := b2e593993
               grind)
            | exact resolve b2e1025241 b2e593993
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e593993 b2e1025241
          have b2e1025666 : y = (M.op x (τ x)) := by
            first
            | (have r₁ := b2e1025554
               have r₂ := b2e53
               grind)
            | exact resolve b2e1025554 b2e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1025554
          have b2e1050205 : (τ (σ x)) = (k x (τ x)) ∨ x = y := by
            first
            | (have i₁ := b2e1025226 x
               have i₂ := b2e610283
               grind)
            | exact superpose b2e610283 b2e1025226
            | (have j0 := b2e1025226 x
               grind)
            | exact resolve b2e1025226 b2e610283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e610283 b2e1025226
          have b2e1050227 : (τ (σ x)) = (k x (τ x)) := by
            first
            | (have r₁ := b2e1050205
               have r₂ := b2e53
               grind)
            | exact resolve b2e1050205 b2e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1050205
          have b2e1050246 : x = (k x (τ x)) := by
            first
            | (have i₁ := b2e1050227
               have i₂ := b2e14 x
               grind)
            | exact superpose b2e14 b2e1050227
            | exact resolve b2e1050227 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1050227
          have b2e1050323 : (σ x) = (σ (M.op (τ x) x)) ∨ y = (τ x) ∨ (τ x) = (M.op x (τ x)) := by
            first
            | (have i₁ := b2e113835 x (τ x)
               have i₂ := b2e1050246
               grind)
            | exact superpose b2e1050246 b2e113835
            | (have j0 := b2e113835 x (τ x)
               grind)
            | exact resolve b2e113835 b2e1050246
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e113835 b2e1050246
          have b2e1050324 : (σ x) = (σ (M.op x (τ x))) ∨ y = (τ x) ∨ (τ x) = (M.op x (τ x)) := by
            first
            | (have i₁ := b2e1050323
               have i₂ := b2e1049 (τ x)
               grind)
            | exact superpose b2e1049 b2e1050323
            | exact resolve b2e1050323 b2e1049
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1049 b2e1050323
          have b2e1050336 : (σ x) = (σ y) ∨ y = (τ x) ∨ (τ x) = (M.op x (τ x)) := by
            first
            | (have i₁ := b2e1050324
               have i₂ := b2e1025666
               grind)
            | exact superpose b2e1025666 b2e1050324
            | exact resolve b2e1050324 b2e1025666
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1050324
          have b2e1050348 : y = (σ x) ∨ y = (τ x) ∨ (τ x) = (M.op x (τ x)) := by
            first
            | (have i₁ := b2e1050336
               have i₂ := b2e2593
               grind)
            | exact superpose b2e2593 b2e1050336
            | exact resolve b2e1050336 b2e2593
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1050336
          have b2e1050360 : y = (τ x) ∨ (τ x) = (M.op x (τ x)) := by
            first
            | (have r₁ := b2e1050348
               have r₂ := b2e617069
               grind)
            | exact resolve b2e1050348 b2e617069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e617069 b2e1050348
          have b2e1050369 : y = (τ x) ∨ y = (τ x) := by
            first
            | (have i₁ := b2e1050360
               have i₂ := b2e1025666
               grind)
            | exact superpose b2e1025666 b2e1050360
            | exact resolve b2e1050360 b2e1025666
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1025666 b2e1050360
          have b2e1050370 : y = (τ x) := by grind
          clear b2e1050369
          have b2e1050441 : x = (σ y) := by
            first
            | (have i₁ := b2e15 x
               have i₂ := b2e1050370
               grind)
            | exact superpose b2e1050370 b2e15
            | exact resolve b2e15 b2e1050370
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1050370
          have b2e1050720 : x = y := by
            first
            | (have i₁ := b2e2593
               have i₂ := b2e1050441
               grind)
            | exact superpose b2e1050441 b2e2593
            | exact resolve b2e2593 b2e1050441
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2593 b2e1050441
          have b2e1050790 : False := by grind
          exact b2e1050790
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e21 : y = (M.op x x) := by grind
          have b3e23 : (σ y) = (M.op (σ x) (σ y)) := by grind
          have b3e24 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e26 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e20
            | exact resolve b3e20 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e33 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b3e13 x X0 x
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e13
            | exact resolve b3e13 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e40 : y = (M.op y y) := by
            first
            | (have i₁ := b3e33 x
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e33
            | exact resolve b3e33 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e33
          have b3e44 : x = y := by
            first
            | (have i₁ := b3e40
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e40
            | exact resolve b3e40 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e40
          have b3e58 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b3e26
               have i₂ := b3e44
               grind)
            | exact superpose b3e44 b3e26
            | exact resolve b3e26 b3e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e26
          have b3e62 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b3e58
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e58
            | exact resolve b3e58 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e58
          have b3e63 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b3e62
               have i₂ := b3e44
               grind)
            | exact superpose b3e44 b3e62
            | exact resolve b3e62 b3e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e44 b3e62
          have b3e64 : False := by grind
          exact b3e64
        · rcases eq_or_ne (M.op y x) (x) with h2b | h2b
          · have b4e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
              intro X0 X1 X2
              grind
            have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b4e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b4e22 : y = (M.op x x) := by grind
            have b4e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b4e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
            have b4e25 : x ≠ (M.op y y) := by grind
            have b4e26 : x = (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e28 : (σ (M.op x y)) ≠ (σ y) := by
              first
              | (have i₁ := b4e21
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e21
              | exact resolve b4e21 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e29 : x = (k x y) := by grind
            have b4e32 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 x)) := by
              intro X0
              first
              | (have i₁ := b4e14 x X0 x
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e14
              | exact resolve b4e14 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e40 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
              intro X0
              grind
            have b4e41 : y = (M.op y y) := by
              first
              | (have i₁ := b4e32 x
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e32
              | exact resolve b4e32 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e42 : (M.op x y) = (M.op y x) := by
              first
              | (have i₁ := b4e32 y
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e32
              | exact resolve b4e32 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e32
            have b4e46 : x = (M.op x y) := by
              first
              | (have i₁ := b4e42
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e42
              | exact resolve b4e42 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e42
            have b4e49 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b4e18 (σ x) (σ y)
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e18
              | (have j0 := b4e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b4e18 (σ x) (σ y)
                 have r₂ := b4e24
                 grind)
              | exact resolve b4e18 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e52 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
            clear b4e49
            have b4e55 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
              first
              | (have r₁ := b4e52
                 have r₂ := b4e23
                 grind)
              | exact resolve b4e52 b4e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e52
            have b4e57 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b4e55
                 have i₂ := b4e20 x y
                 grind)
              | exact superpose b4e20 b4e55
              | exact resolve b4e55 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e55
            have b4e59 : (σ x) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b4e57
                 have i₂ := b4e29
                 grind)
              | exact superpose b4e29 b4e57
              | exact resolve b4e57 b4e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e29 b4e57
            have b4e74 : x ≠ y := by
              first
              | (have i₁ := b4e25
                 have i₂ := b4e41
                 grind)
              | exact superpose b4e41 b4e25
              | exact resolve b4e25 b4e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e41
            have b4e92 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b4e28
                 have i₂ := b4e46
                 grind)
              | exact superpose b4e46 b4e28
              | exact resolve b4e28 b4e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e28 b4e46
            have b4e196 : (σ x) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b4e40 (σ y)
                 have i₂ := b4e59
                 grind)
              | exact superpose b4e59 b4e40
              | exact resolve b4e40 b4e59
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e40 b4e59
            have b4e203 : (σ x) = (σ (k x x)) := by
              first
              | (have i₁ := b4e196
                 have i₂ := b4e20 x x
                 grind)
              | exact superpose b4e20 b4e196
              | exact resolve b4e196 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e196
            have b4e205 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b4e203
                 have i₂ := b4e19 x x
                 grind)
              | exact superpose b4e19 b4e203
              | (have j1 := b4e19 x x
                 grind)
              | exact resolve b4e203 b4e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e203
            have b4e209 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
            clear b4e205
            have b4e213 : (σ x) = (σ y) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b4e209
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e209
              | exact resolve b4e209 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e209
            have b4e214 : x = (M.op x x) := by
              first
              | (have r₁ := b4e213
                 have r₂ := b4e92
                 grind)
              | exact resolve b4e213 b4e92
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e92 b4e213
            have b4e244 : x = y := by
              first
              | (have i₁ := b4e22
                 have i₂ := b4e214
                 grind)
              | exact superpose b4e214 b4e22
              | exact resolve b4e22 b4e214
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e214
            have b4e257 : False := by grind
            exact b4e257
          · have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b5e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b5e22 : y = (M.op x x) := by grind
            have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b5e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
            have b5e25 : x ≠ (M.op y y) := by grind
            have b5e26 : x ≠ (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e28 : (σ (M.op x y)) ≠ (σ y) := by
              first
              | (have i₁ := b5e21
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e21
              | exact resolve b5e21 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e29 : x = (k x y) := by grind
            have b5e44 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b5e18 (σ x) (σ y)
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e18
              | (have j0 := b5e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b5e18 (σ x) (σ y)
                 have r₂ := b5e24
                 grind)
              | exact resolve b5e18 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e47 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
            clear b5e44
            have b5e49 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
              first
              | (have r₁ := b5e47
                 have r₂ := b5e23
                 grind)
              | exact resolve b5e47 b5e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e47
            have b5e50 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b5e49
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e49
              | exact resolve b5e49 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e49
            have b5e51 : (σ x) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b5e50
                 have i₂ := b5e29
                 grind)
              | exact superpose b5e29 b5e50
              | exact resolve b5e50 b5e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e29 b5e50
            have b5e70 : (σ y) = (k (σ y) (σ x)) := by grind
            clear b5e51
            have b5e74 : (σ y) = (σ (k y x)) := by
              first
              | (have i₁ := b5e70
                 have i₂ := b5e20 y x
                 grind)
              | exact superpose b5e20 b5e70
              | exact resolve b5e70 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e70
            have b5e85 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b5e74
                 have i₂ := b5e19 y x
                 grind)
              | exact superpose b5e19 b5e74
              | (have j1 := b5e19 y x
                 grind)
              | exact resolve b5e74 b5e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e74
            have b5e92 : x = (M.op y y) ∨ x = (M.op y x) := by
              first
              | (have r₁ := b5e85
                 have r₂ := b5e28
                 grind)
              | exact resolve b5e85 b5e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e28 b5e85
            have b5e93 : x = (M.op y x) := by
              first
              | (have r₁ := b5e92
                 have r₂ := b5e25
                 grind)
              | exact resolve b5e92 b5e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e92
            have b5e94 : False := by grind
            exact b5e94
      · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : y = (M.op x x) := by grind
          have b6e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b6e24 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e30 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b6e13 x X0 x
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e13
            | exact resolve b6e13 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e31 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b6e13 y X0 y
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e13
            | exact resolve b6e13 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e33 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op x X0) y) := by
            intro X0
            first
            | (have i₁ := b6e13 X0 x x
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e13
            | exact resolve b6e13 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e37 : y = (M.op y y) := by
            first
            | (have i₁ := b6e30 x
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e30
            | exact resolve b6e30 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e30
          have b6e41 : x = y := by
            first
            | (have i₁ := b6e37
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e37
            | exact resolve b6e37 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e37
          have b6e49 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e23
               have i₂ := b6e41
               grind)
            | exact superpose b6e41 b6e23
            | exact resolve b6e23 b6e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e68 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b6e22
               have i₂ := b6e18 (σ x) X0
               grind)
            | (have i₁ := b6e22
               have i₂ := b6e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b6e18 b6e22
            | (have j1 := b6e18 (σ x) X0
               grind)
            | (have r₁ := b6e22
               have r₂ := b6e18 (σ x) (σ y)
               grind)
            | exact resolve b6e22 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e69 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b6e68 X0
               have i₂ := b6e41
               grind)
            | exact superpose b6e41 b6e68
            | (have j0 := b6e68 X0
               grind)
            | exact resolve b6e68 b6e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e68
          have b6e81 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op y X0) (M.op X1 x)) := by
            intro X0 X1
            first
            | (have i₁ := b6e13 (M.op X0 y) X1 x
               have i₂ := b6e31 X0
               grind)
            | exact superpose b6e31 b6e13
            | exact resolve b6e13 b6e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e31
          have b6e82 : ∀ X0 X1 : G, (M.op (M.op X0 x) X1) = (M.op (M.op x X0) (M.op X1 x)) := by
            intro X0 X1
            first
            | (have i₁ := b6e81 X0 X1
               have i₂ := b6e41
               grind)
            | exact superpose b6e41 b6e81
            | exact resolve b6e81 b6e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e81
          have b6e85 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b6e82 X0 X1
               have i₂ := b6e13 X0 X1 x
               grind)
            | exact superpose b6e13 b6e82
            | exact resolve b6e82 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e82
          have b6e100 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op (M.op y X1) (M.op X0 x)) := by
            intro X0 X1
            first
            | (have i₁ := b6e13 X1 (M.op x X0) y
               have i₂ := b6e33 X0
               grind)
            | exact superpose b6e33 b6e13
            | exact resolve b6e13 b6e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e33
          have b6e103 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op (M.op x X1) (M.op X0 x)) := by
            intro X0 X1
            first
            | (have i₁ := b6e100 X0 X1
               have i₂ := b6e41
               grind)
            | exact superpose b6e41 b6e100
            | exact resolve b6e100 b6e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e100
          have b6e110 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b6e103 X0 X1
               have i₂ := b6e13 X1 X0 x
               grind)
            | exact superpose b6e13 b6e103
            | exact resolve b6e103 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e103
          have b6e145 : ∀ X0 X1 : G, (M.op x X1) = (M.op X0 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b6e13 x X1 X0
               have i₂ := b6e85 X0 (M.op X1 X0)
               grind)
            | exact superpose b6e85 b6e13
            | exact resolve b6e13 b6e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e85
          have b6e270 : ∀ X0 : G, (M.op X0 X0) = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b6e110 X0 X0
               have i₂ := b6e145 X0 x
               grind)
            | exact superpose b6e145 b6e110
            | exact resolve b6e110 b6e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e110 b6e145
          have b6e284 : ∀ X0 : G, (M.op X0 X0) = y := by
            intro X0
            first
            | (have i₁ := b6e270 X0
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e270
            | exact resolve b6e270 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e270
          have b6e297 : ∀ X0 : G, (M.op X0 X0) = x := by
            intro X0
            first
            | (have i₁ := b6e284 X0
               have i₂ := b6e41
               grind)
            | exact superpose b6e41 b6e284
            | exact resolve b6e284 b6e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e41 b6e284
          have b6e621 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            grind
          clear b6e297
          have b6e1093 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have j0 := b6e69 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e69
          have b6e1094 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
            first
            | (have r₁ := b6e1093
               have r₂ := b6e49
               grind)
            | exact resolve b6e1093 b6e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1093
          have b6e1095 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
            first
            | (have i₁ := b6e1094
               have i₂ := b6e19 x x
               grind)
            | exact superpose b6e19 b6e1094
            | exact resolve b6e1094 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1094
          have b6e1096 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e1095
               have i₂ := b6e621 x
               grind)
            | exact superpose b6e621 b6e1095
            | exact resolve b6e1095 b6e621
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e621 b6e1095
          have b6e1097 : False := by grind
          exact b6e1097
        · rcases eq_or_ne (M.op y x) (x) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
              intro X0 X1 X2
              grind
            have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b7e22 : y = (M.op x x) := by grind
            have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b7e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
            have b7e26 : x = (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e28 : x = (k x y) := by grind
            have b7e31 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 x)) := by
              intro X0
              first
              | (have i₁ := b7e14 x X0 x
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e14
              | exact resolve b7e14 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e32 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 y)) := by
              intro X0
              first
              | (have i₁ := b7e14 x X0 y
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e14
              | exact resolve b7e14 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X0))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e14 (M.op X1 X2) X3 (M.op X2 X0)
                 have i₂ := b7e14 X0 X1 X2
                 grind)
              | exact superpose b7e14 b7e14
              | exact resolve b7e14 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e34 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op x X0) y) := by
              intro X0
              first
              | (have i₁ := b7e14 X0 x x
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e14
              | exact resolve b7e14 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e35 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x X0) x) := by
              intro X0
              first
              | (have i₁ := b7e14 X0 y x
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e14
              | exact resolve b7e14 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op (M.op X1 X3) X2) (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e14 X2 (M.op X3 X0) (M.op X1 X3)
                 have i₂ := b7e14 X0 X1 X3
                 grind)
              | exact superpose b7e14 b7e14
              | exact resolve b7e14 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e38 : y = (M.op y y) := by
              first
              | (have i₁ := b7e31 x
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e31
              | exact resolve b7e31 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e39 : (M.op x y) = (M.op y x) := by
              first
              | (have i₁ := b7e31 y
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e31
              | exact resolve b7e31 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e43 : x = (M.op x y) := by
              first
              | (have i₁ := b7e39
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e39
              | exact resolve b7e39 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e39
            have b7e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b7e23
                 have i₂ := b7e19 (σ x) X0
                 grind)
              | (have i₁ := b7e23
                 have i₂ := b7e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b7e19 b7e23
              | (have j1 := b7e19 (σ x) X0
                 grind)
              | (have r₁ := b7e23
                 have r₂ := b7e19 (σ x) (σ y)
                 grind)
              | exact resolve b7e23 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e68 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op y X0) y) := by
              intro X0
              first
              | (have i₁ := b7e14 X0 y y
                 have i₂ := b7e38
                 grind)
              | exact superpose b7e38 b7e14
              | exact resolve b7e14 b7e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e69 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 y)) := by
              intro X0
              first
              | (have i₁ := b7e14 y X0 y
                 have i₂ := b7e38
                 grind)
              | exact superpose b7e38 b7e14
              | exact resolve b7e14 b7e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e38
            have b7e72 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op x X0) (M.op X1 x)) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 (M.op X0 y) X1 x
                 have i₂ := b7e32 X0
                 grind)
              | exact superpose b7e32 b7e14
              | exact resolve b7e14 b7e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e32
            have b7e73 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 y) X1) := by
              intro X0 X1
              first
              | (have i₁ := b7e72 X0 X1
                 have i₂ := b7e14 X0 X1 x
                 grind)
              | exact superpose b7e14 b7e72
              | exact resolve b7e72 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e72
            have b7e81 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op (M.op y X1) (M.op X0 x)) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 X1 (M.op x X0) y
                 have i₂ := b7e34 X0
                 grind)
              | exact superpose b7e34 b7e14
              | exact resolve b7e14 b7e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e94 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op x (M.op x X0)) := by
              intro X0
              first
              | (have i₁ := b7e31 (M.op x X0)
                 have i₂ := b7e35 X0
                 grind)
              | exact superpose b7e35 b7e31
              | exact resolve b7e31 b7e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e35
            have b7e100 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op x X0)) := by
              intro X0
              first
              | (have i₁ := b7e94 X0
                 have i₂ := b7e69 X0
                 grind)
              | exact superpose b7e69 b7e94
              | exact resolve b7e94 b7e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e69 b7e94
            have b7e162 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op X1 x)) = (M.op (M.op x X0) X1) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 (M.op x X0) X1 x
                 have i₂ := b7e100 X0
                 grind)
              | exact superpose b7e100 b7e14
              | exact resolve b7e14 b7e100
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e163 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op (M.op x X0) X1) := by
              intro X0 X1
              first
              | (have i₁ := b7e162 X0 X1
                 have i₂ := b7e81 X1 X0
                 grind)
              | exact superpose b7e81 b7e162
              | exact resolve b7e162 b7e81
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e81 b7e162
            have b7e188 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op y X0) X1) := by
              intro X0 X1
              first
              | (have i₁ := b7e73 (M.op y X0) X1
                 have i₂ := b7e68 X0
                 grind)
              | exact superpose b7e68 b7e73
              | exact resolve b7e73 b7e68
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e191 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op (M.op y X1) (M.op X0 y)) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 X1 (M.op y X0) y
                 have i₂ := b7e68 X0
                 grind)
              | exact superpose b7e68 b7e14
              | exact resolve b7e14 b7e68
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e68
            have b7e194 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op y X0)) := by
              intro X0 X1
              first
              | (have i₁ := b7e191 X0 X1
                 have i₂ := b7e14 X1 X0 y
                 grind)
              | exact superpose b7e14 b7e191
              | exact resolve b7e191 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e191
            have b7e197 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y X0) X1) := by
              intro X0 X1
              first
              | (have i₁ := b7e188 X0 X1
                 have i₂ := b7e73 X0 X1
                 grind)
              | exact superpose b7e73 b7e188
              | exact resolve b7e188 b7e73
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e188
            have b7e230 : ∀ X0 X1 : G, (M.op (M.op X1 X0) y) = (M.op (M.op x X1) (M.op x X0)) := by
              intro X0 X1
              first
              | (have i₁ := b7e33 x X1 X0 y
                 have i₂ := b7e31 X0
                 grind)
              | exact superpose b7e31 b7e33
              | exact resolve b7e33 b7e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e31
            have b7e237 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op X2 (M.op X1 (M.op X0 X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b7e73 X2 (M.op X1 (M.op X0 X2))
                 have i₂ := b7e33 X2 y X0 X1
                 grind)
              | exact superpose b7e33 b7e73
              | exact resolve b7e73 b7e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e33 b7e73
            have b7e247 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X1 (M.op X0 X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b7e237 X0 X1 X2
                 have i₂ := b7e197 X0 X1
                 grind)
              | exact superpose b7e197 b7e237
              | exact resolve b7e237 b7e197
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e237
            have b7e253 : ∀ X0 X1 : G, (M.op (M.op X1 X0) y) = (M.op X1 (M.op x (M.op x X0))) := by
              intro X0 X1
              first
              | (have i₁ := b7e230 X0 X1
                 have i₂ := b7e163 X1 (M.op x X0)
                 grind)
              | exact superpose b7e163 b7e230
              | exact resolve b7e230 b7e163
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e163 b7e230
            have b7e278 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op (M.op X1 X0) y) := by
              intro X0 X1
              first
              | (have i₁ := b7e253 X0 X1
                 have i₂ := b7e100 X0
                 grind)
              | exact superpose b7e100 b7e253
              | exact resolve b7e253 b7e100
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e100 b7e253
            have b7e290 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) y) := by
              intro X0 X1
              first
              | (have i₁ := b7e278 X0 X1
                 have i₂ := b7e194 X0 X1
                 grind)
              | exact superpose b7e194 b7e278
              | exact resolve b7e278 b7e194
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e194 b7e278
            have b7e318 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b7e34 X0
                 have i₂ := b7e290 X0 x
                 grind)
              | exact superpose b7e290 b7e34
              | exact resolve b7e34 b7e290
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e34
            have b7e367 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X1))) = (M.op (M.op (M.op y X3) X2) (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e36 (M.op X0 X1) y X2 X3
                 have i₂ := b7e290 X1 X0
                 grind)
              | exact superpose b7e290 b7e36
              | exact resolve b7e36 b7e290
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e36 b7e290
            have b7e392 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 X1)) = (M.op X2 (M.op X3 (M.op X0 X1))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e367 X0 X1 X2 X3
                 have i₂ := b7e197 X3 X2
                 grind)
              | exact superpose b7e197 b7e367
              | exact resolve b7e367 b7e197
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e197 b7e367
            have b7e515 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 x) (M.op X1 x)) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 X0 X1 x
                 have i₂ := b7e318 X0
                 grind)
              | (have i₁ := b7e14 x X1 X0
                 have i₂ := b7e318 X0
                 grind)
              | exact superpose b7e318 b7e14
              | exact resolve b7e14 b7e318
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e318
            have b7e552 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op X0 (M.op X1 x))) := by
              intro X0 X1
              first
              | (have i₁ := b7e515 X0 X1
                 have i₂ := b7e392 X1 x x X0
                 grind)
              | exact superpose b7e392 b7e515
              | exact resolve b7e515 b7e392
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e392 b7e515
            have b7e562 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              first
              | (have i₁ := b7e552 X0 X1
                 have i₂ := b7e247 X1 X0 x
                 grind)
              | exact superpose b7e247 b7e552
              | exact resolve b7e552 b7e247
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e247 b7e552
            have b7e656 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have j0 := b7e65 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e65
            have b7e657 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
              first
              | (have r₁ := b7e656
                 have r₂ := b7e24
                 grind)
              | exact resolve b7e656 b7e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e656
            have b7e658 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b7e657
                 have i₂ := b7e562 (σ y) (σ x)
                 grind)
              | (have i₁ := b7e657
                 have i₂ := b7e562 (σ x) (σ y)
                 grind)
              | exact superpose b7e562 b7e657
              | exact resolve b7e657 b7e562
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e562 b7e657
            have b7e659 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b7e658
                 have i₂ := b7e20 x y
                 grind)
              | exact superpose b7e20 b7e658
              | exact resolve b7e658 b7e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e658
            have b7e660 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b7e659
                 have i₂ := b7e28
                 grind)
              | exact superpose b7e28 b7e659
              | exact resolve b7e659 b7e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e28 b7e659
            have b7e960 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b7e21
                 have i₂ := b7e660
                 grind)
              | exact superpose b7e660 b7e21
              | exact resolve b7e21 b7e660
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e660
            have b7e980 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b7e960
                 have i₂ := b7e43
                 grind)
              | exact superpose b7e43 b7e960
              | exact resolve b7e960 b7e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e43 b7e960
            have b7e981 : False := by grind
            exact b7e981
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
              intro X0 X1 X2
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : y = (M.op x x) := by grind
            have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e31 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 x)) := by
              intro X0
              first
              | (have i₁ := b8e14 x X0 x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X0))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e14 (M.op X1 X2) X3 (M.op X2 X0)
                 have i₂ := b8e14 X0 X1 X2
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e33 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op x X0) y) := by
              intro X0
              first
              | (have i₁ := b8e14 X0 x x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op (M.op X1 X3) X2) (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e14 X2 (M.op X3 X0) (M.op X1 X3)
                 have i₂ := b8e14 X0 X1 X3
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e35 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
              intro X0
              grind
            have b8e36 : y = (M.op y y) := by
              first
              | (have i₁ := b8e31 x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e31
              | exact resolve b8e31 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e46 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op y X0) y) := by
              intro X0
              first
              | (have i₁ := b8e14 X0 y y
                 have i₂ := b8e36
                 grind)
              | exact superpose b8e36 b8e14
              | exact resolve b8e14 b8e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e47 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 y)) := by
              intro X0
              first
              | (have i₁ := b8e14 y X0 y
                 have i₂ := b8e36
                 grind)
              | exact superpose b8e36 b8e14
              | exact resolve b8e14 b8e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e36
            have b8e53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b8e20 X1 X0
                 have i₂ := b8e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b8e19 b8e20
              | (have j1 := b8e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b8e20 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e80 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op (M.op y X1) (M.op X0 y)) := by
              intro X0 X1
              first
              | (have i₁ := b8e14 X1 (M.op y X0) y
                 have i₂ := b8e46 X0
                 grind)
              | exact superpose b8e46 b8e14
              | exact resolve b8e14 b8e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e46
            have b8e83 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op y X0)) := by
              intro X0 X1
              first
              | (have i₁ := b8e80 X0 X1
                 have i₂ := b8e14 X1 X0 y
                 grind)
              | exact superpose b8e14 b8e80
              | exact resolve b8e80 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e80
            have b8e102 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op y X0) (M.op X1 y)) := by
              intro X0 X1
              first
              | (have i₁ := b8e14 (M.op X0 y) X1 y
                 have i₂ := b8e47 X0
                 grind)
              | exact superpose b8e47 b8e14
              | exact resolve b8e14 b8e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e103 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 y) X1) := by
              intro X0 X1
              first
              | (have i₁ := b8e102 X0 X1
                 have i₂ := b8e14 X0 X1 y
                 grind)
              | exact superpose b8e14 b8e102
              | exact resolve b8e102 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e102
            have b8e119 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op X1 (M.op X0 y)) := by
              intro X0 X1
              first
              | (have i₁ := b8e83 (M.op X0 y) X1
                 have i₂ := b8e47 X0
                 grind)
              | exact superpose b8e47 b8e83
              | exact resolve b8e83 b8e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e47
            have b8e128 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X0)) = (M.op (M.op y X1) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14 (M.op y X1) X2 X0
                 have i₂ := b8e83 X1 X0
                 grind)
              | exact superpose b8e83 b8e14
              | exact resolve b8e14 b8e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e131 : (M.op x y) = (M.op y x) := by
              first
              | (have i₁ := b8e31 y
                 have i₂ := b8e83 x y
                 grind)
              | exact superpose b8e83 b8e31
              | exact resolve b8e31 b8e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e133 : ∀ X1 X2 : G, (M.op X1 X2) = (M.op (M.op y X1) X2) := by
              intro X1 X2
              first
              | (have i₁ := b8e128 x X1 X2
                 have i₂ := b8e14 X1 X2 x
                 grind)
              | exact superpose b8e14 b8e128
              | exact resolve b8e128 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e128
            have b8e137 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 y)) := by
              intro X0 X1
              first
              | (have i₁ := b8e119 X0 X1
                 have i₂ := b8e83 X0 X1
                 grind)
              | exact superpose b8e83 b8e119
              | exact resolve b8e119 b8e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e119
            have b8e165 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X3 X0)) = (M.op (M.op X3 X2) (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e32 X3 X2 X1 (M.op X3 X0)
                 have i₂ := b8e14 X0 X1 X3
                 grind)
              | exact superpose b8e14 b8e32
              | exact resolve b8e32 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e219 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) (M.op X1 (M.op X0 y))) := by
              intro X0 X1
              first
              | (have i₁ := b8e32 y x X0 X1
                 have i₂ := b8e131
                 grind)
              | exact superpose b8e131 b8e32
              | exact resolve b8e32 b8e131
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e131
            have b8e226 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x (M.op X1 (M.op X0 y))) := by
              intro X0 X1
              first
              | (have i₁ := b8e219 X0 X1
                 have i₂ := b8e103 x (M.op X1 (M.op X0 y))
                 grind)
              | exact superpose b8e103 b8e219
              | exact resolve b8e219 b8e103
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e219
            have b8e228 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x (M.op X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b8e226 X0 X1
                 have i₂ := b8e137 X0 X1
                 grind)
              | exact superpose b8e137 b8e226
              | exact resolve b8e226 b8e137
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e226
            have b8e235 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) X1) (M.op X2 (M.op x X0))) = (M.op X1 (M.op y X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e34 X2 (M.op x X0) X1 y
                 have i₂ := b8e33 X0
                 grind)
              | exact superpose b8e33 b8e34
              | exact resolve b8e34 b8e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e238 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 x) X2)) = (M.op (M.op (M.op x X0) X1) (M.op X2 y)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e34 X2 y X1 (M.op X0 x)
                 have i₂ := b8e31 X0
                 grind)
              | exact superpose b8e31 b8e34
              | exact resolve b8e34 b8e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e251 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op (M.op X1 X4) X3) X2) (M.op X0 X1)) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b8e34 (M.op X4 X0) (M.op X1 X4) X2 X3
                 have i₂ := b8e14 X0 X1 X4
                 grind)
              | exact superpose b8e14 b8e34
              | exact resolve b8e34 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e254 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x X0))) = (M.op (M.op (M.op y X2) X1) (M.op X0 x)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e34 (M.op x X0) y X1 X2
                 have i₂ := b8e33 X0
                 grind)
              | exact superpose b8e33 b8e34
              | exact resolve b8e34 b8e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e33
            have b8e257 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 y)) = (M.op (M.op (M.op (M.op X0 x) X2) X1) (M.op x X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e34 y (M.op X0 x) X1 X2
                 have i₂ := b8e31 X0
                 grind)
              | exact superpose b8e31 b8e34
              | exact resolve b8e34 b8e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e31
            have b8e264 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) (M.op (M.op X4 X1) X0)) = (M.op (M.op X4 X3) (M.op X0 (M.op X1 X2))) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b8e32 X4 X3 X2 (M.op (M.op X4 X1) X0)
                 have i₂ := b8e34 X2 X4 X0 X1
                 grind)
              | exact superpose b8e34 b8e32
              | exact resolve b8e32 b8e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e32 b8e34
            have b8e283 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 y)) = (M.op (M.op x (M.op (M.op X0 x) X2)) (M.op X0 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e257 X0 X1 X2
                 have i₂ := b8e165 X0 X1 (M.op (M.op X0 x) X2) x
                 grind)
              | (have i₁ := b8e257 X1 X2 X2
                 have i₂ := b8e165 x X1 X2 (M.op (M.op X1 x) X2)
                 grind)
              | exact superpose b8e165 b8e257
              | exact resolve b8e257 b8e165
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e257
            have b8e286 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x X0))) = (M.op (M.op X1 x) (M.op (M.op y X2) X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e254 X0 X1 X2
                 have i₂ := b8e165 X0 x X1 (M.op y X2)
                 grind)
              | (have i₁ := b8e254 x X1 X2
                 have i₂ := b8e165 x X1 (M.op y X2) x
                 grind)
              | exact superpose b8e165 b8e254
              | exact resolve b8e254 b8e165
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e254
            have b8e289 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X0))) = (M.op (M.op X2 X1) (M.op (M.op (M.op X1 X4) X3) X0)) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b8e251 X0 X1 X2 X3 X4
                 have i₂ := b8e165 X0 X1 X2 (M.op (M.op X1 X4) X3)
                 grind)
              | (have i₁ := b8e251 X3 X0 X1 X3 X4
                 have i₂ := b8e165 X0 X1 (M.op (M.op X0 X4) X3) X3
                 grind)
              | exact superpose b8e165 b8e251
              | exact resolve b8e251 b8e165
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e251
            have b8e297 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 x) X2)) = (M.op (M.op X1 y) (M.op (M.op x X0) X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e238 X0 X1 X2
                 have i₂ := b8e165 X2 y X1 (M.op x X0)
                 grind)
              | (have i₁ := b8e238 X0 X1 x
                 have i₂ := b8e165 y X1 (M.op x X0) x
                 grind)
              | exact superpose b8e165 b8e238
              | exact resolve b8e238 b8e165
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e238
            have b8e299 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 x) X1) (M.op X2 (M.op x X0))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e235 X0 X1 X2
                 have i₂ := b8e83 X2 X1
                 grind)
              | exact superpose b8e83 b8e235
              | exact resolve b8e235 b8e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e83 b8e235
            have b8e308 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 y)) = (M.op (M.op X0 x) (M.op X1 (M.op (M.op X0 x) X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e283 X0 X1 X2
                 have i₂ := b8e165 X1 (M.op (M.op X0 x) X2) x X0
                 grind)
              | (have i₁ := b8e283 X0 X1 X2
                 have i₂ := b8e165 X0 X1 (M.op (M.op X0 x) X2) x
                 grind)
              | exact superpose b8e165 b8e283
              | exact resolve b8e283 b8e165
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e165 b8e283
            have b8e310 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x X0))) = (M.op (M.op X1 x) (M.op X2 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e286 X0 X1 X2
                 have i₂ := b8e133 X2 X0
                 grind)
              | (have i₁ := b8e286 X2 X1 X2
                 have i₂ := b8e133 (M.op y X2) X2
                 grind)
              | exact superpose b8e133 b8e286
              | exact resolve b8e286 b8e133
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e133 b8e286
            have b8e316 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 x) X2)) = (M.op X1 (M.op (M.op x X0) X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e297 X0 X1 X2
                 have i₂ := b8e103 X1 (M.op (M.op x X0) X2)
                 grind)
              | exact superpose b8e103 b8e297
              | exact resolve b8e297 b8e103
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e103 b8e297
            have b8e318 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X0) (M.op (M.op (M.op X0 x) x) X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e299 X0 X1 X2
                 have i₂ := b8e264 X2 x X0 X1 (M.op X0 x)
                 grind)
              | exact superpose b8e264 b8e299
              | exact resolve b8e299 b8e264
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e264 b8e299
            have b8e325 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 x) (M.op X1 (M.op (M.op X0 x) X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e308 X0 X1 X2
                 have i₂ := b8e137 X2 X1
                 grind)
              | exact superpose b8e137 b8e308
              | exact resolve b8e308 b8e137
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e137 b8e308
            have b8e328 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 x) X2)) = (M.op X1 (M.op x (M.op X2 X0))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e316 X0 X1 X2
                 have i₂ := b8e228 X0 X2
                 grind)
              | exact superpose b8e228 b8e316
              | exact resolve b8e316 b8e228
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e228 b8e316
            have b8e330 : ∀ X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op x (M.op x X2))) := by
              intro X1 X2
              first
              | (have i₁ := b8e318 x X1 X2
                 have i₂ := b8e289 X2 x X1 x x
                 grind)
              | exact superpose b8e289 b8e318
              | exact resolve b8e318 b8e289
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e289 b8e318
            have b8e336 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X1 (M.op x (M.op (M.op X0 x) X2)))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e325 X0 X1 X2
                 have i₂ := b8e310 (M.op (M.op X0 x) X2) X0 X1
                 grind)
              | exact superpose b8e310 b8e325
              | exact resolve b8e325 b8e310
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e310 b8e325
            have b8e339 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X1 (M.op x (M.op x (M.op X2 X0))))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e336 X0 X1 X2
                 have i₂ := b8e328 X0 x X2
                 grind)
              | exact superpose b8e328 b8e336
              | exact resolve b8e336 b8e328
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e328 b8e336
            have b8e340 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e339 X0 X1 X2
                 have i₂ := b8e330 X1 (M.op X2 X0)
                 grind)
              | (have i₁ := b8e339 X0 X1 X2
                 have i₂ := b8e330 X1 (M.op x (M.op x (M.op X2 X0)))
                 grind)
              | exact superpose b8e330 b8e339
              | exact resolve b8e339 b8e330
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e339
            have b8e997 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b8e53 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e53
            have b8e998 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b8e997 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e997
            have b8e2831 : ∀ X0 : G, (M.op X0 X0) = (M.op x x) := by
              intro X0
              first
              | (have i₁ := b8e330 X0 X0
                 have i₂ := b8e340 X0 x x
                 grind)
              | exact superpose b8e340 b8e330
              | exact resolve b8e330 b8e340
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e330 b8e340
            have b8e2875 : ∀ X0 : G, (M.op X0 X0) = y := by
              intro X0
              first
              | (have i₁ := b8e2831 X0
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e2831
              | exact resolve b8e2831 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e2831
            have b8e3068 : y ≠ (σ y) := by
              first
              | (have i₁ := b8e23
                 have i₂ := b8e2875 (σ x)
                 grind)
              | exact superpose b8e2875 b8e23
              | exact resolve b8e23 b8e2875
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e11614 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b8e998 (M.op X0 X0)
                 have i₂ := b8e35 X0
                 grind)
              | exact superpose b8e35 b8e998
              | (have j0 := b8e998 (M.op X0 X0)
                 grind)
              | exact resolve b8e998 b8e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e35 b8e998
            have b8e11621 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
              intro X0
              first
              | (have j0 := b8e11614 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e11614
            have b8e11635 : ∀ X0 : G, y = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b8e11621 X0
                 have i₂ := b8e2875 (σ (M.op X0 X0))
                 grind)
              | exact superpose b8e2875 b8e11621
              | exact resolve b8e11621 b8e2875
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e11621
            have b8e11651 : y = (σ y) := by
              first
              | (have i₁ := b8e11635 x
                 have i₂ := b8e2875 x
                 grind)
              | exact superpose b8e2875 b8e11635
              | exact resolve b8e11635 b8e2875
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e2875 b8e11635
            have b8e11662 : False := by grind
            exact b8e11662
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e21 : y ≠ (M.op x x) := by grind
          have b9e23 : (σ y) = (M.op (σ x) (σ x)) := by grind
          have b9e24 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e45 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b9e13 y X0 y
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e13
            | exact resolve b9e13 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e52 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            grind
          have b9e68 : x = (M.op x x) := by
            first
            | (have i₁ := b9e45 y
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e45
            | exact resolve b9e45 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e45
          have b9e91 : x ≠ y := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e68
               grind)
            | exact superpose b9e68 b9e21
            | exact resolve b9e21 b9e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e68
          have b9e138 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b9e52 (σ x)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e52
            | exact resolve b9e52 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e52
          have b9e145 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b9e138
               have i₂ := b9e19 y y
               grind)
            | exact superpose b9e19 b9e138
            | exact resolve b9e138 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e138
          have b9e149 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b9e14 (k y y)
               have i₂ := b9e145
               grind)
            | exact superpose b9e145 b9e14
            | exact resolve b9e14 b9e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e145
          have b9e151 : y = (k y y) := by
            first
            | (have i₁ := b9e149
               have i₂ := b9e14 y
               grind)
            | exact superpose b9e14 b9e149
            | exact resolve b9e149 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e149
          have b9e174 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b9e18 y y
               have i₂ := b9e151
               grind)
            | exact superpose b9e151 b9e18
            | (have j0 := b9e18 y y
               grind)
            | exact resolve b9e18 b9e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e151
          have b9e175 : y = (M.op y y) := by grind
          clear b9e174
          have b9e177 : x = y := by
            first
            | (have i₁ := b9e175
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e175
            | exact resolve b9e175 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e175
          have b9e179 : False := by grind
          exact b9e179
        · rcases eq_or_ne (M.op y x) (x) with h2b | h2b
          · have b10e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
              intro X0 X1 X2
              grind
            have b10e23 : y = (M.op x y) := by grind
            have b10e25 : x ≠ (M.op y y) := by grind
            have b10e26 : x = (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e47 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 x)) := by
              intro X0
              first
              | (have i₁ := b10e14 y X0 x
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e14
              | exact resolve b10e14 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e54 : (M.op y y) = (M.op y x) := by
              first
              | (have i₁ := b10e47 y
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e47
              | exact resolve b10e47 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e47
            have b10e59 : x = (M.op y y) := by
              first
              | (have i₁ := b10e54
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e54
              | exact resolve b10e54 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e54
            have b10e60 : False := by grind
            exact b10e60
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : y ≠ (M.op x x) := by grind
            have b11e23 : y = (M.op x y) := by grind
            have b11e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b11e25 : x ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e29 : (σ x) = (k (σ x) (σ y)) := by grind
            have b11e30 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b11e29
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e29
              | exact resolve b11e29 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e29
            have b11e31 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 (k x y)
                 have i₂ := b11e30
                 grind)
              | exact superpose b11e30 b11e15
              | exact resolve b11e15 b11e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e30
            have b11e32 : x = (k x y) := by
              first
              | (have i₁ := b11e31
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e31
              | exact resolve b11e31 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e31
            have b11e58 : y ≠ y ∨ y = (M.op x x) ∨ (M.op y y) = (k x y) := by
              first
              | (have i₁ := b11e18 x y
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e18
              | (have j0 := b11e18 x y
                 grind)
              | (have r₁ := b11e18 x y
                 have r₂ := b11e23
                 grind)
              | exact resolve b11e18 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e60 : y = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
            clear b11e58
            have b11e62 : (M.op y y) = (k x y) := by
              first
              | (have r₁ := b11e60
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e60 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e60
            have b11e63 : x = (M.op y y) := by
              first
              | (have i₁ := b11e62
                 have i₂ := b11e32
                 grind)
              | exact superpose b11e32 b11e62
              | exact resolve b11e62 b11e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e32 b11e62
            have b11e64 : False := by grind
            exact b11e64
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
          · have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e23 : y = (M.op x y) := by grind
            have b12e25 : (σ y) = (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e28 : (σ (M.op x y)) ≠ (σ y) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e21
              | exact resolve b12e21 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e29 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b12e28
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e28
              | exact resolve b12e28 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e28
            have b12e30 : False := by grind
            exact b12e30
          · rcases eq_or_ne (M.op y x) (x) with h2b | h2b
            · have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e24 : y = (M.op x y) := by grind
              have b13e26 : (σ y) = (M.op (σ x) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e30 : (σ (M.op x y)) ≠ (σ y) := by
                first
                | (have i₁ := b13e22
                   have i₂ := b13e26
                   grind)
                | exact superpose b13e26 b13e22
                | exact resolve b13e22 b13e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e31 : (σ y) ≠ (σ y) := by
                first
                | (have i₁ := b13e30
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e30
                | exact resolve b13e30 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e30
              have b13e32 : False := by grind
              exact b13e32
            · have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e24 : y = (M.op x y) := by grind
              have b14e26 : (σ y) = (M.op (σ x) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e30 : (σ (M.op x y)) ≠ (σ y) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e22
                | exact resolve b14e22 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e31 : (σ y) ≠ (σ y) := by
                first
                | (have i₁ := b14e30
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e30
                | exact resolve b14e30 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e30
              have b14e32 : False := by grind
              exact b14e32
        · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
              intro X0 X1 X2
              grind
            have b15e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b15e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b15e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e22 : y ≠ (M.op x x) := by grind
            have b15e23 : y = (M.op x y) := by grind
            have b15e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b15e25 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
            have b15e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e29 : y = (k y x) := by grind
            have b15e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b15e20 X1 (τ X0)
                 have i₂ := b15e16 X0
                 grind)
              | exact superpose b15e16 b15e20
              | exact resolve b15e20 b15e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e38 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 x)) := by
              intro X0
              first
              | (have i₁ := b15e14 y X0 x
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e14
              | exact resolve b15e14 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e39 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op X0 y)) := by
              intro X0
              first
              | (have i₁ := b15e14 y X0 y
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e14
              | exact resolve b15e14 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X0))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b15e14 (M.op X1 X2) X3 (M.op X2 X0)
                 have i₂ := b15e14 X0 X1 X2
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e42 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op y X0) x) := by
              intro X0
              first
              | (have i₁ := b15e14 X0 y y
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e14
              | exact resolve b15e14 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e43 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op (M.op X1 X3) X2) (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b15e14 X2 (M.op X3 X0) (M.op X1 X3)
                 have i₂ := b15e14 X0 X1 X3
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e46 : ∀ X0 X1 : G, (M.op (M.op X0 x) X1) = (M.op (M.op y X0) (M.op X1 y)) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 (M.op X0 x) X1 y
                 have i₂ := b15e38 X0
                 grind)
              | exact superpose b15e38 b15e14
              | exact resolve b15e14 b15e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e38
            have b15e47 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 x) X1) := by
              intro X0 X1
              first
              | (have i₁ := b15e46 X0 X1
                 have i₂ := b15e14 X0 X1 y
                 grind)
              | exact superpose b15e14 b15e46
              | exact resolve b15e46 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e46
            have b15e49 : y ≠ y ∨ y = (M.op x x) ∨ (M.op y y) = (k x y) := by
              first
              | (have i₁ := b15e18 x y
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e18
              | (have j0 := b15e18 x y
                 grind)
              | (have r₁ := b15e18 x y
                 have r₂ := b15e23
                 grind)
              | exact resolve b15e18 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e53 : y = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
            clear b15e49
            have b15e55 : (M.op y y) = (k x y) := by
              first
              | (have r₁ := b15e53
                 have r₂ := b15e22
                 grind)
              | exact resolve b15e53 b15e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e53
            have b15e57 : x = (k x y) := by
              first
              | (have i₁ := b15e55
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e55
              | exact resolve b15e55 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e55
            have b15e67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b15e69 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X2 X1) X0) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X2 X0) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e14 X1 X2 X2
                 have i₂ := b15e19 X2 X0
                 grind)
              | (have i₁ := b15e14 X0 X1 X2
                 have i₂ := b15e19 X0 (M.op X1 X2)
                 grind)
              | exact superpose b15e19 b15e14
              | (have j1 := b15e19 X2 X0
                 grind)
              | exact resolve b15e14 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e71 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op (M.op X1 X1) X0) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X1 X1 X1
                 have i₂ := b15e19 (M.op X1 X1) X0
                 grind)
              | (have i₁ := b15e14 X0 X1 x
                 have i₂ := b15e19 X0 (M.op (M.op x X0) (M.op X1 x))
                 grind)
              | exact superpose b15e19 b15e14
              | (have j1 := b15e19 (M.op X1 X1) X0
                 grind)
              | exact resolve b15e14 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e72 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b15e24
                 have i₂ := b15e19 (σ x) X0
                 grind)
              | (have i₁ := b15e24
                 have i₂ := b15e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b15e19 b15e24
              | (have j1 := b15e19 (σ x) X0
                 grind)
              | (have r₁ := b15e24
                 have r₂ := b15e19 (σ x) (σ y)
                 grind)
              | exact resolve b15e24 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e73 : (M.op x y) = (M.op y x) := by
              first
              | (have i₁ := b15e39 x
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e39
              | exact resolve b15e39 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e74 : x = (M.op x x) := by
              first
              | (have i₁ := b15e39 y
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e39
              | exact resolve b15e39 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e39
            have b15e79 : y = (M.op y x) := by
              first
              | (have i₁ := b15e73
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e73
              | exact resolve b15e73 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e73
            have b15e90 : x ≠ y := by
              first
              | (have i₁ := b15e22
                 have i₂ := b15e74
                 grind)
              | exact superpose b15e74 b15e22
              | exact resolve b15e22 b15e74
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e93 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 x)) := by
              intro X0
              first
              | (have i₁ := b15e14 x X0 x
                 have i₂ := b15e74
                 grind)
              | exact superpose b15e74 b15e14
              | exact resolve b15e14 b15e74
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e98 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op (M.op x X1) (M.op X0 y)) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X1 (M.op y X0) x
                 have i₂ := b15e42 X0
                 grind)
              | exact superpose b15e42 b15e14
              | exact resolve b15e14 b15e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e109 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e15 (k X0 (τ X1))
                 have i₂ := b15e31 X1 X0
                 grind)
              | exact superpose b15e31 b15e15
              | exact resolve b15e15 b15e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e31
            have b15e149 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op x X0) (M.op X1 y)) := by
              intro X0 X1
              first
              | (have i₁ := b15e40 x X0 y X1
                 have i₂ := b15e79
                 grind)
              | exact superpose b15e79 b15e40
              | exact resolve b15e40 b15e79
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e153 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X3 X0)) = (M.op (M.op X3 X2) (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b15e40 X3 X2 X1 (M.op X3 X0)
                 have i₂ := b15e14 X0 X1 X3
                 grind)
              | exact superpose b15e14 b15e40
              | exact resolve b15e40 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e167 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op X0 (M.op y X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e149 X0 X1
                 have i₂ := b15e98 X1 X0
                 grind)
              | exact superpose b15e98 b15e149
              | exact resolve b15e149 b15e98
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e98 b15e149
            have b15e175 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op y X0) X1) := by
              intro X0 X1
              first
              | (have i₁ := b15e47 (M.op y X0) X1
                 have i₂ := b15e42 X0
                 grind)
              | exact superpose b15e42 b15e47
              | exact resolve b15e47 b15e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e181 : ∀ X0 X1 : G, (M.op x X1) = (M.op X0 (M.op X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 x X1 X0
                 have i₂ := b15e47 X0 (M.op X1 X0)
                 grind)
              | exact superpose b15e47 b15e14
              | exact resolve b15e14 b15e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e191 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 x)) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e14 X2 (M.op X0 x) X1
                 have i₂ := b15e47 X0 X1
                 grind)
              | exact superpose b15e47 b15e14
              | exact resolve b15e14 b15e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e192 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X1) (M.op X2 (M.op X0 x))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e14 X1 X2 (M.op X0 x)
                 have i₂ := b15e47 X0 X1
                 grind)
              | exact superpose b15e47 b15e14
              | exact resolve b15e14 b15e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e193 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X0 x)) = (M.op (M.op X2 X3) (M.op X0 (M.op X1 X2))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b15e40 X2 X3 X1 (M.op X0 x)
                 have i₂ := b15e47 X0 (M.op X1 X2)
                 grind)
              | exact superpose b15e47 b15e40
              | exact resolve b15e40 b15e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e196 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) X0) = (M.op (M.op X3 X1) (M.op X0 x)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b15e193 X0 X1 x X3
                 have i₂ := b15e40 x X3 X1 X0
                 grind)
              | exact superpose b15e40 b15e193
              | exact resolve b15e193 b15e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e193
            have b15e197 : ∀ X0 X2 : G, (M.op X2 X0) = (M.op X2 (M.op X0 x)) := by
              intro X0 X2
              first
              | (have i₁ := b15e191 X0 x X2
                 have i₂ := b15e14 X2 X0 x
                 grind)
              | exact superpose b15e14 b15e191
              | exact resolve b15e191 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e191
            have b15e206 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op y X0) X1) := by
              intro X0 X1
              first
              | (have i₁ := b15e175 X0 X1
                 have i₂ := b15e167 X0 X1
                 grind)
              | exact superpose b15e167 b15e175
              | exact resolve b15e175 b15e167
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e167 b15e175
            have b15e226 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X0)) = (M.op X1 (M.op x X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e43 X2 X0 X1 x
                 have i₂ := b15e47 X0 X1
                 grind)
              | exact superpose b15e47 b15e43
              | exact resolve b15e43 b15e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e242 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op (M.op y X1) X0) y) := by
              intro X0 X1
              first
              | (have i₁ := b15e43 x y X0 X1
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e43
              | exact resolve b15e43 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e247 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 X2)) = (M.op x (M.op X0 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e47 (M.op X2 X0) (M.op X1 X2)
                 have i₂ := b15e43 X1 X2 x X0
                 grind)
              | exact superpose b15e43 b15e47
              | exact resolve b15e47 b15e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e262 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e247 X0 X1 x
                 have i₂ := b15e14 X0 X1 x
                 grind)
              | exact superpose b15e14 b15e247
              | exact resolve b15e247 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e247
            have b15e267 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op X1 (M.op y X0)) y) := by
              intro X0 X1
              first
              | (have i₁ := b15e242 X0 X1
                 have i₂ := b15e206 X1 X0
                 grind)
              | exact superpose b15e206 b15e242
              | exact resolve b15e242 b15e206
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e206 b15e242
            have b15e278 : ∀ X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op x X2)) := by
              intro X1 X2
              first
              | (have i₁ := b15e226 x X1 X2
                 have i₂ := b15e14 X1 X2 x
                 grind)
              | exact superpose b15e14 b15e226
              | exact resolve b15e226 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e226
            have b15e293 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 (M.op y X0)) y) := by
              intro X0 X1
              first
              | (have i₁ := b15e267 X0 X1
                 have i₂ := b15e197 X1 X0
                 grind)
              | (have i₁ := b15e267 x X1
                 have i₂ := b15e197 (M.op X1 x) x
                 grind)
              | exact superpose b15e197 b15e267
              | exact resolve b15e267 b15e197
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e267
            have b15e370 : ∀ X0 X1 : G, (M.op X1 x) = (M.op (M.op (M.op X0 x) X1) (M.op x X0)) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X1 x (M.op X0 x)
                 have i₂ := b15e93 X0
                 grind)
              | exact superpose b15e93 b15e14
              | exact resolve b15e14 b15e93
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e374 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 x)) = (M.op (M.op (M.op (M.op X0 x) X2) X1) (M.op x X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e43 x (M.op X0 x) X1 X2
                 have i₂ := b15e93 X0
                 grind)
              | exact superpose b15e93 b15e43
              | exact resolve b15e43 b15e93
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e93
            have b15e377 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 x)) = (M.op (M.op x (M.op (M.op X0 x) X2)) (M.op X0 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e374 X0 X1 X2
                 have i₂ := b15e153 X0 X1 (M.op (M.op X0 x) X2) x
                 grind)
              | (have i₁ := b15e374 X1 X2 X2
                 have i₂ := b15e153 x X1 X2 (M.op (M.op X1 x) X2)
                 grind)
              | exact superpose b15e153 b15e374
              | exact resolve b15e374 b15e153
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e374
            have b15e381 : ∀ X0 X1 : G, (M.op X1 x) = (M.op (M.op x (M.op X0 x)) (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e370 X0 X1
                 have i₂ := b15e153 X0 X1 (M.op X0 x) x
                 grind)
              | (have i₁ := b15e370 X1 x
                 have i₂ := b15e153 x X1 x (M.op X1 x)
                 grind)
              | exact superpose b15e153 b15e370
              | exact resolve b15e370 b15e153
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e370
            have b15e388 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 x)) = (M.op (M.op X0 x) (M.op X1 (M.op (M.op X0 x) X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e377 X0 X1 X2
                 have i₂ := b15e153 X1 (M.op (M.op X0 x) X2) x X0
                 grind)
              | (have i₁ := b15e377 X0 X1 X2
                 have i₂ := b15e153 X0 X1 (M.op (M.op X0 x) X2) x
                 grind)
              | exact superpose b15e153 b15e377
              | exact resolve b15e377 b15e153
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e377
            have b15e391 : ∀ X0 X1 : G, (M.op X1 x) = (M.op (M.op X0 x) (M.op X1 (M.op X0 x))) := by
              intro X0 X1
              first
              | (have i₁ := b15e381 X0 X1
                 have i₂ := b15e153 X1 (M.op X0 x) x X0
                 grind)
              | (have i₁ := b15e381 X0 X1
                 have i₂ := b15e153 X0 X1 (M.op X0 x) x
                 grind)
              | exact superpose b15e153 b15e381
              | exact resolve b15e381 b15e153
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e381
            have b15e394 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 x)) = (M.op X0 (M.op X1 (M.op (M.op X0 x) X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e388 X0 X1 X2
                 have i₂ := b15e47 X0 (M.op X1 (M.op (M.op X0 x) X2))
                 grind)
              | exact superpose b15e47 b15e388
              | exact resolve b15e388 b15e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e388
            have b15e397 : ∀ X1 : G, (M.op X1 x) = (M.op x X1) := by
              intro X1
              first
              | (have i₁ := b15e391 x X1
                 have i₂ := b15e192 x x X1
                 grind)
              | exact superpose b15e192 b15e391
              | exact resolve b15e391 b15e192
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e192 b15e391
            have b15e398 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 x)) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e394 X0 X1 X2
                 have i₂ := b15e47 X0 X2
                 grind)
              | exact superpose b15e47 b15e394
              | exact resolve b15e394 b15e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e394
            have b15e400 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e398 X0 X1 X2
                 have i₂ := b15e197 X2 X1
                 grind)
              | (have i₁ := b15e398 X0 X2 X2
                 have i₂ := b15e197 (M.op X2 x) X2
                 grind)
              | exact superpose b15e197 b15e398
              | exact resolve b15e398 b15e197
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e398
            have b15e401 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have j0 := b15e72 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e72
            have b15e402 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
              first
              | (have r₁ := b15e401
                 have r₂ := b15e25
                 grind)
              | exact resolve b15e401 b15e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e401
            have b15e403 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b15e402
                 have i₂ := b15e20 x y
                 grind)
              | exact superpose b15e20 b15e402
              | exact resolve b15e402 b15e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e402
            have b15e404 : (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b15e403
                 have i₂ := b15e57
                 grind)
              | exact superpose b15e57 b15e403
              | exact resolve b15e403 b15e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e403
            have b15e419 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op y X0)) := by
              intro X0
              first
              | (have i₁ := b15e42 X0
                 have i₂ := b15e397 (M.op y X0)
                 grind)
              | exact superpose b15e397 b15e42
              | exact resolve b15e42 b15e397
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e42
            have b15e426 : ∀ X0 X1 : G, (M.op X1 x) = (M.op (M.op X0 X1) (M.op X0 x)) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X1 x X0
                 have i₂ := b15e397 X0
                 grind)
              | (have i₁ := b15e14 X0 X1 x
                 have i₂ := b15e397 X1
                 grind)
              | exact superpose b15e397 b15e14
              | exact resolve b15e14 b15e397
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e428 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 x) (M.op X2 (M.op X1 x))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e40 x X0 X1 X2
                 have i₂ := b15e397 X0
                 grind)
              | (have i₁ := b15e40 X1 x X2 x
                 have i₂ := b15e397 X1
                 grind)
              | exact superpose b15e397 b15e40
              | exact resolve b15e40 b15e397
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e436 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op X2 (M.op X1 x))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e428 X0 X1 X2
                 have i₂ := b15e47 X0 (M.op X2 (M.op X1 x))
                 grind)
              | exact superpose b15e47 b15e428
              | exact resolve b15e428 b15e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e47 b15e428
            have b15e438 : ∀ X0 X1 : G, (M.op X1 x) = (M.op (M.op X0 X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b15e426 X0 X1
                 have i₂ := b15e196 X0 X1 X0
                 grind)
              | (have i₁ := b15e426 x X1
                 have i₂ := b15e196 (M.op x x) X1 x
                 grind)
              | exact superpose b15e196 b15e426
              | exact resolve b15e426 b15e196
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e196 b15e426
            have b15e442 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b15e419 X0
                 have i₂ := b15e262 y X0
                 grind)
              | exact superpose b15e262 b15e419
              | exact resolve b15e419 b15e262
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e262 b15e419
            have b15e454 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op X2 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e436 X0 X1 X2
                 have i₂ := b15e197 X1 X2
                 grind)
              | (have i₁ := b15e436 X0 X1 X2
                 have i₂ := b15e197 (M.op X1 x) X2
                 grind)
              | exact superpose b15e197 b15e436
              | exact resolve b15e436 b15e197
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e436
            have b15e498 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X1 X0))) ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X1 X2) = X2 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b15e14 X2 X3 (M.op X1 X0)
                 have i₂ := b15e69 X2 X0 X1
                 grind)
              | exact superpose b15e69 b15e14
              | (have j1 := b15e69 X2 X1 X1
                 grind)
              | exact resolve b15e14 b15e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e69
            have b15e521 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X1 X1) X3) ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X1 X2) = X2 := by
              intro X1 X2 X3
              first
              | (have i₁ := b15e498 x X1 X2 X3
                 have i₂ := b15e40 x X1 X1 X3
                 grind)
              | exact superpose b15e40 b15e498
              | (have j0 := b15e498 x X1 X2 X3
                 grind)
              | exact resolve b15e498 b15e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e40 b15e498
            have b15e555 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op X1 (M.op X3 X1)) ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X1 X2) = X2 := by
              intro X1 X2 X3
              first
              | (have i₁ := b15e521 X1 X2 X3
                 have i₂ := b15e454 X1 X1 X3
                 grind)
              | exact superpose b15e454 b15e521
              | (have j0 := b15e521 X1 X2 X3
                 grind)
              | exact resolve b15e521 b15e454
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e521
            have b15e583 : ∀ X1 X2 X3 : G, (k X1 X2) = (M.op X2 X1) ∨ (M.op X2 X3) = (M.op x X3) ∨ (M.op X1 X2) = X2 := by
              intro X1 X2 X3
              first
              | (have i₁ := b15e555 X1 X2 X3
                 have i₂ := b15e181 X1 X3
                 grind)
              | exact superpose b15e181 b15e555
              | (have j0 := b15e555 X1 X2 X3
                 grind)
              | exact resolve b15e555 b15e181
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e555
            have b15e876 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ x) X0) (σ x)) := by
              intro X0
              first
              | (have i₁ := b15e14 X0 (σ y) (σ x)
                 have i₂ := b15e404
                 grind)
              | exact superpose b15e404 b15e14
              | exact resolve b15e14 b15e404
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e877 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
              first
              | (have i₁ := b15e18 (σ y) (σ x)
                 have i₂ := b15e404
                 grind)
              | exact superpose b15e404 b15e18
              | (have j0 := b15e18 (σ y) (σ x)
                 grind)
              | (have r₁ := b15e18 (σ y) (σ x)
                 have r₂ := b15e404
                 grind)
              | exact resolve b15e18 b15e404
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e884 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by grind
            clear b15e877
            have b15e889 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b15e884
                 have i₂ := b15e20 y x
                 grind)
              | exact superpose b15e20 b15e884
              | exact resolve b15e884 b15e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e884
            have b15e890 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b15e876 X0
                 have i₂ := b15e438 (σ x) X0
                 grind)
              | exact superpose b15e438 b15e876
              | exact resolve b15e876 b15e438
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e438 b15e876
            have b15e894 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b15e889
                 have i₂ := b15e29
                 grind)
              | exact superpose b15e29 b15e889
              | exact resolve b15e889 b15e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e29 b15e889
            have b15e898 : (σ x) = (M.op (σ y) (σ y)) := by
              first
              | (have r₁ := b15e894
                 have r₂ := b15e24
                 grind)
              | exact resolve b15e894 b15e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e894
            have b15e901 : (σ x) = (M.op (σ y) x) := by
              first
              | (have i₁ := b15e898
                 have i₂ := b15e890 (σ y)
                 grind)
              | exact superpose b15e890 b15e898
              | exact resolve b15e898 b15e890
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e898
            have b15e903 : (σ x) = (M.op x (σ y)) := by
              first
              | (have i₁ := b15e901
                 have i₂ := b15e397 (σ y)
                 grind)
              | exact superpose b15e397 b15e901
              | exact resolve b15e901 b15e397
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e901
            have b15e904 : (σ x) = (M.op x x) := by
              first
              | (have i₁ := b15e903
                 have i₂ := b15e890 x
                 grind)
              | exact superpose b15e890 b15e903
              | exact resolve b15e903 b15e890
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e903
            have b15e905 : x = (σ x) := by
              first
              | (have i₁ := b15e904
                 have i₂ := b15e74
                 grind)
              | exact superpose b15e74 b15e904
              | exact resolve b15e904 b15e74
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e904
            have b15e914 : ∀ X0 : G, (M.op X0 x) = (k x X0) ∨ x = X0 ∨ (M.op x X0) = X0 := by
              intro X0
              first
              | (have i₁ := b15e71 X0 y
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e71
              | exact resolve b15e71 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e71
            have b15e954 : x = (τ x) := by
              first
              | (have i₁ := b15e15 x
                 have i₂ := b15e905
                 grind)
              | exact superpose b15e905 b15e15
              | exact resolve b15e15 b15e905
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e1566 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op X1 X0)) = (M.op (σ y) X1) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 (σ y) X1 X0
                 have i₂ := b15e890 X0
                 grind)
              | exact superpose b15e890 b15e14
              | exact resolve b15e14 b15e890
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e1572 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) X1) (M.op X2 X0)) = (M.op X1 (M.op (σ y) X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e43 X2 X0 X1 (σ y)
                 have i₂ := b15e890 X0
                 grind)
              | exact superpose b15e890 b15e43
              | exact resolve b15e43 b15e890
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e43
            have b15e1601 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ y) X2)) = (M.op (M.op X1 X0) (M.op (M.op X0 x) X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e1572 X0 X1 X2
                 have i₂ := b15e153 X2 X0 X1 (M.op X0 x)
                 grind)
              | (have i₁ := b15e1572 X0 X1 x
                 have i₂ := b15e153 X0 X1 (M.op X0 x) x
                 grind)
              | exact superpose b15e153 b15e1572
              | exact resolve b15e1572 b15e153
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e153 b15e1572
            have b15e1607 : ∀ X1 : G, (M.op x X1) = (M.op (σ y) X1) := by
              intro X1
              first
              | (have i₁ := b15e1566 x X1
                 have i₂ := b15e14 x X1 x
                 grind)
              | exact superpose b15e14 b15e1566
              | exact resolve b15e1566 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1566
            have b15e1630 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ y) X2)) = (M.op X1 (M.op (M.op (M.op X0 x) X2) X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e1601 X0 X1 X2
                 have i₂ := b15e454 X1 X0 (M.op (M.op X0 x) X2)
                 grind)
              | exact superpose b15e454 b15e1601
              | exact resolve b15e1601 b15e454
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1601
            have b15e1653 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ y) X2)) = (M.op X1 (M.op (M.op X0 x) (M.op X0 X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e1630 X0 X1 X2
                 have i₂ := b15e454 (M.op X0 x) X2 X0
                 grind)
              | exact superpose b15e454 b15e1630
              | exact resolve b15e1630 b15e454
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1630
            have b15e1672 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ y) X2)) = (M.op X1 (M.op X0 (M.op (M.op X0 X2) x))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e1653 X0 X1 X2
                 have i₂ := b15e454 X0 x (M.op X0 X2)
                 grind)
              | exact superpose b15e454 b15e1653
              | exact resolve b15e1653 b15e454
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1653
            have b15e1688 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ y) X2)) = (M.op X1 (M.op X0 (M.op X0 X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e1672 X0 X1 X2
                 have i₂ := b15e197 (M.op X0 X2) X0
                 grind)
              | (have i₁ := b15e1672 X2 X1 X2
                 have i₂ := b15e197 (M.op (M.op X2 X2) x) X2
                 grind)
              | exact superpose b15e197 b15e1672
              | exact resolve b15e1672 b15e197
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1672
            have b15e1701 : ∀ X0 X1 X2 : G, (M.op X1 (M.op x X2)) = (M.op X1 (M.op X0 (M.op X0 X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e1688 X0 X1 X2
                 have i₂ := b15e1607 X2
                 grind)
              | exact superpose b15e1607 b15e1688
              | exact resolve b15e1688 b15e1607
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1607 b15e1688
            have b15e1710 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X0 (M.op X0 X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e1701 X0 X1 X2
                 have i₂ := b15e278 X1 X2
                 grind)
              | (have i₁ := b15e1701 X0 X1 X2
                 have i₂ := b15e278 X1 (M.op x X2)
                 grind)
              | exact superpose b15e278 b15e1701
              | exact resolve b15e1701 b15e278
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e278 b15e1701
            have b15e1995 : ∀ X0 : G, (k x (τ X0)) = (τ (k x X0)) := by
              intro X0
              first
              | (have i₁ := b15e109 x X0
                 have i₂ := b15e905
                 grind)
              | exact superpose b15e905 b15e109
              | exact resolve b15e109 b15e905
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e2218 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 x)) := by
              intro X0
              first
              | (have i₁ := b15e181 X0 x
                 have i₂ := b15e397 X0
                 grind)
              | (have i₁ := b15e181 x x
                 have i₂ := b15e397 x
                 grind)
              | exact superpose b15e397 b15e181
              | exact resolve b15e181 b15e397
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e2315 : ∀ X0 : G, (M.op X0 X0) = (M.op x x) := by
              intro X0
              first
              | (have i₁ := b15e2218 X0
                 have i₂ := b15e197 X0 X0
                 grind)
              | (have i₁ := b15e2218 x
                 have i₂ := b15e197 (M.op x x) x
                 grind)
              | exact superpose b15e197 b15e2218
              | exact resolve b15e2218 b15e197
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e197 b15e2218
            have b15e2337 : ∀ X0 : G, (M.op X0 X0) = x := by
              intro X0
              first
              | (have i₁ := b15e2315 X0
                 have i₂ := b15e74
                 grind)
              | exact superpose b15e74 b15e2315
              | exact resolve b15e2315 b15e74
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e2315
            have b15e3045 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op X0 (M.op y x)) y) := by
              intro X0
              first
              | (have i₁ := b15e293 (σ y) X0
                 have i₂ := b15e890 y
                 grind)
              | exact superpose b15e890 b15e293
              | exact resolve b15e293 b15e890
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e3051 : ∀ X0 X1 : G, (M.op (M.op X0 y) y) = (M.op X1 (M.op X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b15e293 X1 (M.op X1 X0)
                 have i₂ := b15e14 X0 y X1
                 grind)
              | exact superpose b15e14 b15e293
              | exact resolve b15e293 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e3077 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y (M.op X1 (M.op y X0))) := by
              intro X0 X1
              first
              | (have i₁ := b15e442 (M.op X1 (M.op y X0))
                 have i₂ := b15e293 X0 X1
                 grind)
              | exact superpose b15e293 b15e442
              | exact resolve b15e442 b15e293
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e293
            have b15e3104 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              first
              | (have i₁ := b15e3077 X0 X1
                 have i₂ := b15e400 y X1 X0
                 grind)
              | exact superpose b15e400 b15e3077
              | exact resolve b15e3077 b15e400
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e400 b15e3077
            have b15e3122 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op X0 (M.op y y)) := by
              intro X0 X1
              first
              | (have i₁ := b15e3051 X0 X1
                 have i₂ := b15e454 X0 y y
                 grind)
              | exact superpose b15e454 b15e3051
              | exact resolve b15e3051 b15e454
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e3051
            have b15e3128 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op y (M.op y x))) := by
              intro X0
              first
              | (have i₁ := b15e3045 X0
                 have i₂ := b15e454 X0 (M.op y x) y
                 grind)
              | exact superpose b15e454 b15e3045
              | exact resolve b15e3045 b15e454
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e454 b15e3045
            have b15e3158 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 (M.op X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b15e3122 X0 X1
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e3122
              | exact resolve b15e3122 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e3122
            have b15e3163 : ∀ X0 : G, (M.op X0 x) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b15e3128 X0
                 have i₂ := b15e1710 y X0 x
                 grind)
              | exact superpose b15e1710 b15e3128
              | exact resolve b15e3128 b15e1710
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1710 b15e3128
            have b15e3775 : ∀ X0 X1 : G, (M.op x X1) = (M.op X0 (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e181 X0 X1
                 have i₂ := b15e3104 X1 X0
                 grind)
              | (have i₁ := b15e181 X0 X1
                 have i₂ := b15e3104 X0 X1
                 grind)
              | exact superpose b15e3104 b15e181
              | exact resolve b15e181 b15e3104
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e181 b15e3104
            have b15e4153 : ∀ X0 : G, (M.op X0 x) ≠ X0 ∨ (M.op (σ y) (σ y)) = X0 ∨ (M.op X0 X0) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b15e18 (σ y) X0
                 have i₂ := b15e3163 X0
                 grind)
              | exact superpose b15e3163 b15e18
              | (have j0 := b15e18 (σ y) X0
                 grind)
              | exact resolve b15e18 b15e3163
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e3163
            have b15e4210 : ∀ X0 : G, (M.op (σ y) x) = X0 ∨ (M.op X0 x) ≠ X0 ∨ (M.op X0 X0) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b15e4153 X0
                 have i₂ := b15e890 (σ y)
                 grind)
              | exact superpose b15e890 b15e4153
              | (have j0 := b15e4153 X0
                 grind)
              | exact resolve b15e4153 b15e890
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e4153
            have b15e4249 : ∀ X0 : G, (M.op x (σ y)) = X0 ∨ (M.op X0 x) ≠ X0 ∨ (M.op X0 X0) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b15e4210 X0
                 have i₂ := b15e397 (σ y)
                 grind)
              | exact superpose b15e397 b15e4210
              | (have j0 := b15e4210 X0
                 grind)
              | exact resolve b15e4210 b15e397
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e4210
            have b15e4283 : ∀ X0 : G, (M.op x x) = X0 ∨ (M.op X0 x) ≠ X0 ∨ (M.op X0 X0) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b15e4249 X0
                 have i₂ := b15e890 x
                 grind)
              | exact superpose b15e890 b15e4249
              | (have j0 := b15e4249 X0
                 grind)
              | exact resolve b15e4249 b15e890
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e890 b15e4249
            have b15e4302 : ∀ X0 : G, x = X0 ∨ (M.op X0 x) ≠ X0 ∨ (M.op X0 X0) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b15e4283 X0
                 have i₂ := b15e74
                 grind)
              | exact superpose b15e74 b15e4283
              | (have j0 := b15e4283 X0
                 grind)
              | (have r₁ := b15e4283 x
                 have r₂ := b15e74
                 grind)
              | exact resolve b15e4283 b15e74
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e74 b15e4283
            have b15e4312 : ∀ X0 : G, (M.op X0 x) ≠ X0 ∨ x = X0 ∨ x = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b15e4302 X0
                 have i₂ := b15e2337 X0
                 grind)
              | exact superpose b15e2337 b15e4302
              | (have j0 := b15e4302 X0
                 grind)
              | (have r₁ := b15e4302 x
                 have r₂ := b15e2337 x
                 grind)
              | exact resolve b15e4302 b15e2337
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e4302
            have b15e6494 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X1 (M.op X0 X1) X0
                 have i₂ := b15e3158 X0 (M.op X0 X1)
                 grind)
              | exact superpose b15e3158 b15e14
              | exact resolve b15e14 b15e3158
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e3158
            have b15e8617 : (τ x) = (k x (τ y)) := by
              first
              | (have i₁ := b15e1995 y
                 have i₂ := b15e57
                 grind)
              | exact superpose b15e57 b15e1995
              | exact resolve b15e1995 b15e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e57 b15e1995
            have b15e8645 : x = (k x (τ y)) := by
              first
              | (have i₁ := b15e8617
                 have i₂ := b15e954
                 grind)
              | exact superpose b15e954 b15e8617
              | exact resolve b15e8617 b15e954
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e8617
            have b15e71304 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 x) = (k x X0) ∨ (M.op x X0) = X0 := by
              intro X0
              first
              | (have j0 := b15e583 x X0 x
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e583
            have b15e71309 : ∀ X0 : G, x ≠ X0 ∨ (M.op X0 x) = (k x X0) ∨ (M.op x X0) = X0 := by
              intro X0
              first
              | (have i₁ := b15e71304 X0
                 have i₂ := b15e2337 X0
                 grind)
              | exact superpose b15e2337 b15e71304
              | (have j0 := b15e71304 X0
                 grind)
              | (have r₁ := b15e71304 x
                 have r₂ := b15e2337 x
                 grind)
              | exact resolve b15e71304 b15e2337
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e71304
            have b15e71618 : ∀ X0 : G, (M.op X0 x) = (k x X0) ∨ (M.op x X0) = X0 := by
              intro X0
              first
              | (have j0 := b15e71309 X0
                 have j1 := b15e914 X0
                 grind)
              | (have r₁ := b15e71309 X0
                 have r₂ := b15e914 X0
                 grind)
              | (have r₁ := b15e71309 x
                 have r₂ := b15e914 x
                 grind)
              | (have r₁ := b15e71309 (M.op x x)
                 have r₂ := b15e914 x
                 grind)
              | exact resolve b15e71309 b15e914
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e914 b15e71309
            have b15e232362 : x = (M.op (τ y) x) ∨ (τ y) = (M.op x (τ y)) := by
              first
              | (have i₁ := b15e8645
                 have i₂ := b15e71618 (τ y)
                 grind)
              | exact superpose b15e71618 b15e8645
              | (have j1 := b15e71618 (τ y)
                 grind)
              | exact resolve b15e8645 b15e71618
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e8645 b15e71618
            have b15e232441 : (τ y) = (M.op x (τ y)) ∨ x = (M.op x (τ y)) := by
              first
              | (have i₁ := b15e232362
                 have i₂ := b15e397 (τ y)
                 grind)
              | exact superpose b15e397 b15e232362
              | exact resolve b15e232362 b15e397
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e397 b15e232362
            have b15e505262 : y ≠ y ∨ x = y ∨ x = (k (σ y) y) := by
              first
              | (have i₁ := b15e4312 y
                 have i₂ := b15e79
                 grind)
              | exact superpose b15e79 b15e4312
              | (have j0 := b15e4312 y
                 grind)
              | (have r₁ := b15e4312 y
                 have r₂ := b15e79
                 grind)
              | exact resolve b15e4312 b15e79
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e4312
            have b15e505279 : x = y ∨ x = (k (σ y) y) := by grind
            clear b15e505262
            have b15e505290 : x = (k (σ y) y) := by
              first
              | (have r₁ := b15e505279
                 have r₂ := b15e90
                 grind)
              | exact resolve b15e505279 b15e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e505279
            have b15e506928 : (τ x) = (k y (τ y)) := by
              first
              | (have i₁ := b15e109 y y
                 have i₂ := b15e505290
                 grind)
              | exact superpose b15e505290 b15e109
              | exact resolve b15e109 b15e505290
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e109 b15e505290
            have b15e506951 : x = (k y (τ y)) := by
              first
              | (have i₁ := b15e506928
                 have i₂ := b15e954
                 grind)
              | exact superpose b15e954 b15e506928
              | exact resolve b15e506928 b15e954
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e954 b15e506928
            have b15e507557 : x = (M.op (τ y) y) ∨ x = y ∨ (τ y) = (M.op y (τ y)) := by
              first
              | (have i₁ := b15e67 (τ y) y
                 have i₂ := b15e506951
                 grind)
              | exact superpose b15e506951 b15e67
              | (have j0 := b15e67 (τ y) y
                 grind)
              | exact resolve b15e67 b15e506951
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e67 b15e506951
            have b15e507563 : x = (M.op (τ y) y) ∨ (τ y) = (M.op y (τ y)) := by
              first
              | (have r₁ := b15e507557
                 have r₂ := b15e90
                 grind)
              | exact resolve b15e507557 b15e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e507557
            have b15e507579 : (τ y) = (M.op y (τ y)) ∨ x = (M.op y (τ y)) := by
              first
              | (have i₁ := b15e507563
                 have i₂ := b15e442 (τ y)
                 grind)
              | exact superpose b15e442 b15e507563
              | exact resolve b15e507563 b15e442
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e442 b15e507563
            have b15e514803 : (M.op y x) = (M.op (τ y) (τ y)) ∨ x = (M.op y (τ y)) := by
              first
              | (have i₁ := b15e6494 y (τ y)
                 have i₂ := b15e507579
                 grind)
              | exact superpose b15e507579 b15e6494
              | exact resolve b15e6494 b15e507579
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e6494 b15e507579
            have b15e514835 : x = (M.op y x) ∨ x = (M.op y (τ y)) := by
              first
              | (have i₁ := b15e514803
                 have i₂ := b15e2337 (τ y)
                 grind)
              | exact superpose b15e2337 b15e514803
              | exact resolve b15e514803 b15e2337
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e2337 b15e514803
            have b15e514926 : x = y ∨ x = (M.op y (τ y)) := by
              first
              | (have i₁ := b15e514835
                 have i₂ := b15e79
                 grind)
              | exact superpose b15e79 b15e514835
              | exact resolve b15e514835 b15e79
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e514835
            have b15e514985 : x = (M.op y (τ y)) := by
              first
              | (have r₁ := b15e514926
                 have r₂ := b15e90
                 grind)
              | exact resolve b15e514926 b15e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e514926
            have b15e515663 : (M.op y x) = (M.op x (τ y)) := by
              first
              | (have i₁ := b15e3775 y (τ y)
                 have i₂ := b15e514985
                 grind)
              | exact superpose b15e514985 b15e3775
              | exact resolve b15e3775 b15e514985
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e3775 b15e514985
            have b15e515718 : y = (M.op x (τ y)) := by
              first
              | (have i₁ := b15e515663
                 have i₂ := b15e79
                 grind)
              | exact superpose b15e79 b15e515663
              | exact resolve b15e515663 b15e79
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e515663
            have b15e516369 : y = (τ y) ∨ x = y := by
              first
              | (have i₁ := b15e232441
                 have i₂ := b15e515718
                 grind)
              | exact superpose b15e515718 b15e232441
              | exact resolve b15e232441 b15e515718
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e232441 b15e515718
            have b15e516635 : y = (τ y) := by
              first
              | (have r₁ := b15e516369
                 have r₂ := b15e90
                 grind)
              | exact resolve b15e516369 b15e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e516369
            have b15e517077 : y = (σ y) := by
              first
              | (have i₁ := b15e16 y
                 have i₂ := b15e516635
                 grind)
              | exact superpose b15e516635 b15e16
              | exact resolve b15e16 b15e516635
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e516635
            have b15e517415 : (σ x) = (M.op y (σ x)) := by
              first
              | (have i₁ := b15e404
                 have i₂ := b15e517077
                 grind)
              | exact superpose b15e517077 b15e404
              | exact resolve b15e404 b15e517077
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e404 b15e517077
            have b15e517511 : x = (M.op y x) := by
              first
              | (have i₁ := b15e517415
                 have i₂ := b15e905
                 grind)
              | exact superpose b15e905 b15e517415
              | exact resolve b15e517415 b15e905
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e905 b15e517415
            have b15e517531 : x = y := by
              first
              | (have i₁ := b15e517511
                 have i₂ := b15e79
                 grind)
              | exact superpose b15e79 b15e517511
              | exact resolve b15e517511 b15e79
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e79 b15e517511
            have b15e517546 : False := by grind
            exact b15e517546
          · rcases eq_or_ne (M.op y x) (x) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
                intro X0 X1 X2
                grind
              have b16e24 : y = (M.op x y) := by grind
              have b16e27 : x ≠ (M.op y y) := by grind
              have b16e28 : x = (M.op y x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e39 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 x)) := by
                intro X0
                first
                | (have i₁ := b16e15 y X0 x
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e15
                | exact resolve b16e15 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e46 : (M.op y y) = (M.op y x) := by
                first
                | (have i₁ := b16e39 y
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e39
                | exact resolve b16e39 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e39
              have b16e51 : x = (M.op y y) := by
                first
                | (have i₁ := b16e46
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e46
                | exact resolve b16e46 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e46
              have b16e52 : False := by grind
              exact b16e52
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
                intro X0 X1 X2
                grind
              have b17e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b17e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e23 : y ≠ (M.op x x) := by grind
              have b17e24 : y = (M.op x y) := by grind
              have b17e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b17e26 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
              have b17e27 : x ≠ (M.op y y) := by grind
              have b17e28 : x ≠ (M.op y x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e39 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 x)) := by
                intro X0
                first
                | (have i₁ := b17e15 y X0 x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e41 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op y X0) y) := by
                intro X0
                first
                | (have i₁ := b17e15 X0 x y
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e43 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
                intro X0
                grind
              have b17e45 : ∀ X0 X1 : G, (M.op (M.op X0 x) X1) = (M.op (M.op y X0) (M.op X1 y)) := by
                intro X0 X1
                first
                | (have i₁ := b17e15 (M.op X0 x) X1 y
                   have i₂ := b17e39 X0
                   grind)
                | exact superpose b17e39 b17e15
                | exact resolve b17e15 b17e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e39
              have b17e46 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 x) X1) := by
                intro X0 X1
                first
                | (have i₁ := b17e45 X0 X1
                   have i₂ := b17e15 X0 X1 y
                   grind)
                | exact superpose b17e15 b17e45
                | exact resolve b17e45 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e45
              have b17e48 : y ≠ y ∨ y = (M.op x x) ∨ (M.op y y) = (k x y) := by
                first
                | (have i₁ := b17e19 x y
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e19
                | (have j0 := b17e19 x y
                   grind)
                | (have r₁ := b17e19 x y
                   have r₂ := b17e24
                   grind)
                | exact resolve b17e19 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e51 : y = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
              clear b17e48
              have b17e53 : (M.op y y) = (k x y) := by
                first
                | (have r₁ := b17e51
                   have r₂ := b17e23
                   grind)
                | exact resolve b17e51 b17e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e51
              have b17e58 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b17e21 X1 X0
                   have i₂ := b17e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b17e20 b17e21
                | (have j1 := b17e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b17e21 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e61 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b17e66 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
                intro X0
                first
                | (have i₁ := b17e25
                   have i₂ := b17e20 (σ x) X0
                   grind)
                | (have i₁ := b17e25
                   have i₂ := b17e20 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b17e20 b17e25
                | (have j1 := b17e20 (σ x) X0
                   grind)
                | (have r₁ := b17e25
                   have r₂ := b17e20 (σ x) (σ y)
                   grind)
                | exact resolve b17e25 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e85 : ∀ X0 X1 : G, (M.op x X1) = (M.op X0 (M.op X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b17e15 x X1 X0
                   have i₂ := b17e46 X0 (M.op X1 X0)
                   grind)
                | exact superpose b17e46 b17e15
                | exact resolve b17e15 b17e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e86 : (M.op x x) = (M.op y y) := by
                first
                | (have i₁ := b17e41 x
                   have i₂ := b17e46 y y
                   grind)
                | exact superpose b17e46 b17e41
                | exact resolve b17e41 b17e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e41
              have b17e90 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 x)) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 X2 (M.op X0 x) X1
                   have i₂ := b17e46 X0 X1
                   grind)
                | exact superpose b17e46 b17e15
                | exact resolve b17e15 b17e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e46
              have b17e92 : ∀ X0 X2 : G, (M.op X2 X0) = (M.op X2 (M.op X0 x)) := by
                intro X0 X2
                first
                | (have i₁ := b17e90 X0 x X2
                   have i₂ := b17e15 X2 X0 x
                   grind)
                | exact superpose b17e15 b17e90
                | exact resolve b17e90 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e90
              have b17e109 : x ≠ (M.op x x) := by
                first
                | (have i₁ := b17e27
                   have i₂ := b17e86
                   grind)
                | exact superpose b17e86 b17e27
                | exact resolve b17e27 b17e86
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e279 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                first
                | (have j0 := b17e61 X1 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e61
              have b17e283 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have j0 := b17e66 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e66
              have b17e284 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
                first
                | (have r₁ := b17e283
                   have r₂ := b17e26
                   grind)
                | exact resolve b17e283 b17e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e283
              have b17e285 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b17e284
                   have i₂ := b17e21 x y
                   grind)
                | exact superpose b17e21 b17e284
                | exact resolve b17e284 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e284
              have b17e286 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b17e285
                   have i₂ := b17e53
                   grind)
                | exact superpose b17e53 b17e285
                | exact resolve b17e285 b17e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e53 b17e285
              have b17e287 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b17e286
                   have i₂ := b17e86
                   grind)
                | exact superpose b17e86 b17e286
                | exact resolve b17e286 b17e86
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e86 b17e286
              have b17e448 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op X0 X1) (M.op x X0)) := by
                intro X0 X1
                first
                | (have i₁ := b17e85 (M.op X0 X1) X1
                   have i₂ := b17e85 X1 X0
                   grind)
                | exact superpose b17e85 b17e85
                | exact resolve b17e85 b17e85
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e498 : ∀ X1 : G, (M.op X1 x) = (M.op x X1) := by
                intro X1
                first
                | (have i₁ := b17e448 x X1
                   have i₂ := b17e15 X1 x x
                   grind)
                | exact superpose b17e15 b17e448
                | exact resolve b17e448 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e448
              have b17e588 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 x)) := by
                intro X0
                first
                | (have i₁ := b17e85 X0 x
                   have i₂ := b17e498 X0
                   grind)
                | (have i₁ := b17e85 x x
                   have i₂ := b17e498 x
                   grind)
                | exact superpose b17e498 b17e85
                | exact resolve b17e85 b17e498
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e85 b17e498
              have b17e590 : ∀ X0 : G, (M.op X0 X0) = (M.op x x) := by
                intro X0
                first
                | (have i₁ := b17e588 X0
                   have i₂ := b17e92 X0 X0
                   grind)
                | (have i₁ := b17e588 x
                   have i₂ := b17e92 (M.op x x) x
                   grind)
                | exact superpose b17e92 b17e588
                | exact resolve b17e588 b17e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e92 b17e588
              have b17e701 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b17e16 X1
                   have i₂ := b17e58 X1 X0
                   grind)
                | exact superpose b17e58 b17e16
                | (have j1 := b17e58 X1 X0
                   grind)
                | exact resolve b17e16 b17e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e735 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b17e58 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e58
              have b17e736 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b17e735 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e735
              have b17e750 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op x x) := by
                intro X0
                first
                | (have i₁ := b17e736 X0
                   have i₂ := b17e590 (σ X0)
                   grind)
                | exact superpose b17e590 b17e736
                | (have j0 := b17e736 X0
                   grind)
                | exact resolve b17e736 b17e590
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e736
              have b17e776 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (τ (M.op x x)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b17e701 X0 X1
                   have i₂ := b17e590 (σ X0)
                   grind)
                | exact superpose b17e590 b17e701
                | (have j0 := b17e701 X0 X1
                   grind)
                | exact resolve b17e701 b17e590
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e701
              have b17e897 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
                intro X0 X1
                first
                | (have i₁ := b17e590 X0
                   have i₂ := b17e590 X1
                   grind)
                | (have i₁ := b17e590 X0
                   have i₂ := b17e590 x
                   grind)
                | exact superpose b17e590 b17e590
                | exact resolve b17e590 b17e590
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e928 : ∀ X0 : G, (M.op X0 X0) ≠ x := by
                intro X0
                first
                | (have i₁ := b17e109
                   have i₂ := b17e590 X0
                   grind)
                | (have i₁ := b17e109
                   have i₂ := b17e590 x
                   grind)
                | exact superpose b17e590 b17e109
                | exact resolve b17e109 b17e590
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e109 b17e590
              have b17e3222 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op x x) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b17e750 (M.op X0 X0)
                   have i₂ := b17e43 X0
                   grind)
                | exact superpose b17e43 b17e750
                | (have j0 := b17e750 (M.op X0 X0)
                   grind)
                | exact resolve b17e750 b17e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e43 b17e750
              have b17e3227 : ∀ X0 : G, (M.op x x) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have j0 := b17e3222 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3222
              have b17e3302 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op x x)) := by
                intro X0
                first
                | (have i₁ := b17e16 (M.op X0 X0)
                   have i₂ := b17e3227 X0
                   grind)
                | exact superpose b17e3227 b17e16
                | exact resolve b17e16 b17e3227
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e3479 : x ≠ (τ (M.op x x)) := by
                first
                | (have i₁ := b17e928 x
                   have i₂ := b17e3302 x
                   grind)
                | exact superpose b17e3302 b17e928
                | exact resolve b17e928 b17e3302
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e928 b17e3302
              have b17e3638 : ∀ X0 : G, x ≠ (τ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b17e3479
                   have i₂ := b17e897 x X0
                   grind)
                | (have i₁ := b17e3479
                   have i₂ := b17e897 X0 x
                   grind)
                | exact superpose b17e897 b17e3479
                | exact resolve b17e3479 b17e897
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e897
              have b17e10604 : y ≠ y ∨ y = (k y x) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b17e279 y x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e279
                | (have j0 := b17e279 y x
                   grind)
                | (have r₁ := b17e279 y x
                   have r₂ := b17e24
                   grind)
                | exact resolve b17e279 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e279
              have b17e10612 : y = (k y x) ∨ x = (M.op y x) := by grind
              clear b17e10604
              have b17e10617 : y = (k y x) := by
                first
                | (have r₁ := b17e10612
                   have r₂ := b17e28
                   grind)
                | exact resolve b17e10612 b17e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e10612
              have b17e95552 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (τ (M.op x x)) := by
                first
                | (have i₁ := b17e287
                   have i₂ := b17e776 y x
                   grind)
                | exact superpose b17e776 b17e287
                | (have j1 := b17e776 y x
                   grind)
                | exact resolve b17e287 b17e776
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e287 b17e776
              have b17e95687 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
                first
                | (have r₁ := b17e95552
                   have r₂ := b17e3479
                   grind)
                | exact resolve b17e95552 b17e3479
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3479 b17e95552
              have b17e95870 : (σ x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
                first
                | (have i₁ := b17e95687
                   have i₂ := b17e3227 x
                   grind)
                | exact superpose b17e3227 b17e95687
                | exact resolve b17e95687 b17e3227
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3227 b17e95687
              have b17e95991 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op x x) := by
                first
                | (have i₁ := b17e95870
                   have i₂ := b17e10617
                   grind)
                | exact superpose b17e10617 b17e95870
                | exact resolve b17e95870 b17e10617
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e10617 b17e95870
              have b17e96071 : (σ x) = (M.op x x) := by
                first
                | (have r₁ := b17e95991
                   have r₂ := b17e26
                   grind)
                | exact resolve b17e95991 b17e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e95991
              have b17e96355 : x ≠ (τ (σ x)) := by
                first
                | (have i₁ := b17e3638 x
                   have i₂ := b17e96071
                   grind)
                | exact superpose b17e96071 b17e3638
                | exact resolve b17e3638 b17e96071
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3638 b17e96071
              have b17e96485 : False := by grind
              exact b17e96485
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : y ≠ (M.op x x) := by grind
          have b18e23 : (σ y) = (M.op (σ x) (σ x)) := by grind
          have b18e24 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e43 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b18e13 y X0 y
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e13
            | exact resolve b18e13 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e49 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            grind
          have b18e50 : x = (M.op x x) := by
            first
            | (have i₁ := b18e43 y
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e43
            | exact resolve b18e43 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e43
          have b18e59 : x ≠ y := by
            first
            | (have i₁ := b18e21
               have i₂ := b18e50
               grind)
            | exact superpose b18e50 b18e21
            | exact resolve b18e21 b18e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e50
          have b18e115 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b18e49 (σ x)
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e49
            | exact resolve b18e49 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e49
          have b18e122 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b18e115
               have i₂ := b18e19 y y
               grind)
            | exact superpose b18e19 b18e115
            | exact resolve b18e115 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e115
          have b18e138 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b18e14 (k y y)
               have i₂ := b18e122
               grind)
            | exact superpose b18e122 b18e14
            | exact resolve b18e14 b18e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e122
          have b18e140 : y = (k y y) := by
            first
            | (have i₁ := b18e138
               have i₂ := b18e14 y
               grind)
            | exact superpose b18e14 b18e138
            | exact resolve b18e138 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e138
          have b18e162 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b18e18 y y
               have i₂ := b18e140
               grind)
            | exact superpose b18e140 b18e18
            | (have j0 := b18e18 y y
               grind)
            | exact resolve b18e18 b18e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e140
          have b18e163 : y = (M.op y y) := by grind
          clear b18e162
          have b18e165 : x = y := by
            first
            | (have i₁ := b18e163
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e163
            | exact resolve b18e163 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e163
          have b18e167 : False := by grind
          exact b18e167
        · rcases eq_or_ne (M.op y x) (x) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
              intro X0 X1 X2
              grind
            have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : y ≠ (M.op x x) := by grind
            have b19e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b19e26 : x = (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e44 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 y)) := by
              intro X0
              first
              | (have i₁ := b19e14 x X0 y
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e14
              | exact resolve b19e14 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e47 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x X0) x) := by
              intro X0
              first
              | (have i₁ := b19e14 X0 y x
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e14
              | exact resolve b19e14 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e50 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
              intro X0
              grind
            have b19e52 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op x X0) (M.op X1 x)) := by
              intro X0 X1
              first
              | (have i₁ := b19e14 (M.op X0 y) X1 x
                 have i₂ := b19e44 X0
                 grind)
              | exact superpose b19e44 b19e14
              | exact resolve b19e14 b19e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e44
            have b19e53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 y) X1) := by
              intro X0 X1
              first
              | (have i₁ := b19e52 X0 X1
                 have i₂ := b19e14 X0 X1 x
                 grind)
              | exact superpose b19e14 b19e52
              | exact resolve b19e52 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e52
            have b19e100 : (M.op x x) = (M.op y y) := by
              first
              | (have i₁ := b19e47 y
                 have i₂ := b19e53 x x
                 grind)
              | exact superpose b19e53 b19e47
              | exact resolve b19e47 b19e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e47 b19e53
            have b19e118 : (σ y) = (k (σ y) (σ y)) := by
              first
              | (have i₁ := b19e50 (σ x)
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e50
              | exact resolve b19e50 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e50
            have b19e123 : (σ y) = (σ (k y y)) := by
              first
              | (have i₁ := b19e118
                 have i₂ := b19e20 y y
                 grind)
              | exact superpose b19e20 b19e118
              | exact resolve b19e118 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e118
            have b19e128 : (k y y) = (τ (σ y)) := by
              first
              | (have i₁ := b19e15 (k y y)
                 have i₂ := b19e123
                 grind)
              | exact superpose b19e123 b19e15
              | exact resolve b19e15 b19e123
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e123
            have b19e130 : y = (k y y) := by
              first
              | (have i₁ := b19e128
                 have i₂ := b19e15 y
                 grind)
              | exact superpose b19e15 b19e128
              | exact resolve b19e128 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e128
            have b19e145 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b19e19 y y
                 have i₂ := b19e130
                 grind)
              | exact superpose b19e130 b19e19
              | (have j0 := b19e19 y y
                 grind)
              | exact resolve b19e19 b19e130
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e130
            have b19e146 : y = (M.op y y) := by grind
            clear b19e145
            have b19e311 : y = (M.op x x) := by
              first
              | (have i₁ := b19e146
                 have i₂ := b19e100
                 grind)
              | exact superpose b19e100 b19e146
              | exact resolve b19e146 b19e100
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e100 b19e146
            have b19e332 : False := by grind
            exact b19e332
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op x x) := by grind
            have b20e23 : y ≠ (M.op x y) := by grind
            have b20e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b20e26 : x ≠ (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e28 : (σ x) = (k (σ x) (σ y)) := by grind
            have b20e29 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b20e28
                 have i₂ := b20e20 x y
                 grind)
              | exact superpose b20e20 b20e28
              | exact resolve b20e28 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e28
            have b20e30 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b20e15 (k x y)
                 have i₂ := b20e29
                 grind)
              | exact superpose b20e29 b20e15
              | exact resolve b20e15 b20e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e29
            have b20e31 : x = (k x y) := by
              first
              | (have i₁ := b20e30
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e30
              | exact resolve b20e30 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e30
            have b20e78 : x = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b20e31
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e31
              | (have j1 := b20e19 x y
                 grind)
              | exact resolve b20e31 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e31
            have b20e87 : y = (M.op x x) ∨ y = (M.op x y) := by
              first
              | (have r₁ := b20e78
                 have r₂ := b20e26
                 grind)
              | exact resolve b20e78 b20e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e78
            have b20e90 : y = (M.op x y) := by
              first
              | (have r₁ := b20e87
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e87 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e87
            have b20e92 : False := by grind
            exact b20e92
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
              intro X0 X1 X2
              grind
            have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b21e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b21e22 : y ≠ (M.op x x) := by grind
            have b21e23 : y ≠ (M.op x y) := by grind
            have b21e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b21e25 : (σ y) = (M.op (σ x) (σ y)) := by grind
            have b21e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e28 : (σ (M.op x y)) ≠ (σ y) := by
              first
              | (have i₁ := b21e21
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e21
              | exact resolve b21e21 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b21e20 (τ X0) X1
                 have i₂ := b21e16 X0
                 grind)
              | exact superpose b21e16 b21e20
              | exact resolve b21e20 b21e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b21e20 X1 (τ X0)
                 have i₂ := b21e16 X0
                 grind)
              | exact superpose b21e16 b21e20
              | exact resolve b21e20 b21e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e32 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op X0 y)) := by
              intro X0
              first
              | (have i₁ := b21e14 y X0 y
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e14
              | exact resolve b21e14 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e33 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X0 (σ x))) := by
              intro X0
              first
              | (have i₁ := b21e14 (σ y) X0 (σ x)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e14
              | exact resolve b21e14 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X0))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e14 (M.op X1 X2) X3 (M.op X2 X0)
                 have i₂ := b21e14 X0 X1 X2
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e35 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op y X0) x) := by
              intro X0
              first
              | (have i₁ := b21e14 X0 y y
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e14
              | exact resolve b21e14 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e36 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op (σ y) X0) (σ y)) := by
              intro X0
              first
              | (have i₁ := b21e14 X0 (σ x) (σ y)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e14
              | exact resolve b21e14 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e37 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op (M.op X1 X3) X2) (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e14 X2 (M.op X3 X0) (M.op X1 X3)
                 have i₂ := b21e14 X0 X1 X3
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e39 : x = (M.op x x) := by
              first
              | (have i₁ := b21e32 y
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e32
              | exact resolve b21e32 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e44 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b21e18 (σ x) (σ y)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e18
              | (have j0 := b21e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b21e18 (σ x) (σ y)
                 have r₂ := b21e25
                 grind)
              | exact resolve b21e18 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e47 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
            clear b21e44
            have b21e49 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
              first
              | (have r₁ := b21e47
                 have r₂ := b21e24
                 grind)
              | exact resolve b21e47 b21e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e47
            have b21e50 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b21e49
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e49
              | exact resolve b21e49 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e49
            have b21e51 : x ≠ y := by
              first
              | (have i₁ := b21e22
                 have i₂ := b21e39
                 grind)
              | exact superpose b21e39 b21e22
              | exact resolve b21e22 b21e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e52 : x = (k x x) := by grind
            have b21e53 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op x X0) x) := by
              intro X0
              first
              | (have i₁ := b21e14 X0 x x
                 have i₂ := b21e39
                 grind)
              | exact superpose b21e39 b21e14
              | exact resolve b21e14 b21e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e54 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 x)) := by
              intro X0
              first
              | (have i₁ := b21e14 x X0 x
                 have i₂ := b21e39
                 grind)
              | exact superpose b21e39 b21e14
              | exact resolve b21e14 b21e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e60 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b21e20 X1 X0
                 have i₂ := b21e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b21e19 b21e20
              | (have j1 := b21e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b21e20 b21e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e64 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X2 X1)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e14 X1 X2 X1
                 have i₂ := b21e19 X1 X0
                 grind)
              | (have i₁ := b21e14 X0 X1 X2
                 have i₂ := b21e19 X0 (M.op X2 X0)
                 grind)
              | exact superpose b21e19 b21e14
              | (have j1 := b21e19 X1 X0
                 grind)
              | exact resolve b21e14 b21e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e82 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b21e15 (k (τ X0) X1)
                 have i₂ := b21e30 X0 X1
                 grind)
              | exact superpose b21e30 b21e15
              | exact resolve b21e15 b21e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e30
            have b21e84 : ∀ X0 : G, (M.op (M.op y X0) x) = (M.op (M.op X0 y) x) := by
              intro X0
              first
              | (have i₁ := b21e53 (M.op X0 y)
                 have i₂ := b21e32 X0
                 grind)
              | exact superpose b21e32 b21e53
              | exact resolve b21e53 b21e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e87 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op (M.op x X1) (M.op X0 x)) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 X1 (M.op x X0) x
                 have i₂ := b21e53 X0
                 grind)
              | exact superpose b21e53 b21e14
              | exact resolve b21e14 b21e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e90 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op x X0)) := by
              intro X0 X1
              first
              | (have i₁ := b21e87 X0 X1
                 have i₂ := b21e14 X1 X0 x
                 grind)
              | exact superpose b21e14 b21e87
              | exact resolve b21e87 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e87
            have b21e92 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 y) x) := by
              intro X0
              first
              | (have i₁ := b21e84 X0
                 have i₂ := b21e35 X0
                 grind)
              | exact superpose b21e35 b21e84
              | exact resolve b21e84 b21e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e84
            have b21e100 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b21e15 (k X0 (τ X1))
                 have i₂ := b21e31 X1 X0
                 grind)
              | exact superpose b21e31 b21e15
              | exact resolve b21e15 b21e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e109 : ∀ X0 X1 : G, (M.op (M.op X0 x) X1) = (M.op (M.op x X0) (M.op X1 x)) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 (M.op X0 x) X1 x
                 have i₂ := b21e54 X0
                 grind)
              | exact superpose b21e54 b21e14
              | exact resolve b21e14 b21e54
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e110 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 x) X1) := by
              intro X0 X1
              first
              | (have i₁ := b21e109 X0 X1
                 have i₂ := b21e14 X0 X1 x
                 grind)
              | exact superpose b21e14 b21e109
              | exact resolve b21e109 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e109
            have b21e155 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (M.op (σ y) X0) (M.op X1 (σ y))) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 (M.op X0 (σ x)) X1 (σ y)
                 have i₂ := b21e33 X0
                 grind)
              | exact superpose b21e33 b21e14
              | exact resolve b21e14 b21e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e156 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 (σ x)) X1) := by
              intro X0 X1
              first
              | (have i₁ := b21e155 X0 X1
                 have i₂ := b21e14 X0 X1 (σ y)
                 grind)
              | exact superpose b21e14 b21e155
              | exact resolve b21e155 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e155
            have b21e170 : (M.op (σ y) (σ x)) = (M.op (σ (k x y)) (σ y)) := by
              first
              | (have i₁ := b21e36 (σ y)
                 have i₂ := b21e50
                 grind)
              | exact superpose b21e50 b21e36
              | exact resolve b21e36 b21e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e193 : ∀ X0 X1 X2 : G, (M.op (M.op x X1) X2) = (M.op (M.op X0 x) (M.op X2 (M.op X1 (M.op x X0)))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e34 (M.op x X0) x X1 X2
                 have i₂ := b21e53 X0
                 grind)
              | exact superpose b21e53 b21e34
              | exact resolve b21e34 b21e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e201 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op x (M.op X1 (M.op X0 y))) := by
              intro X0 X1
              first
              | (have i₁ := b21e34 y y X0 X1
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e34
              | exact resolve b21e34 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e215 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X2 X3)) = (M.op (M.op X3 X1) X0) ∨ (k (M.op X2 X3) X0) = (M.op X0 (M.op X2 X3)) ∨ (M.op (M.op X2 X3) X0) = X0 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e34 X3 X1 X2 (M.op X2 X3)
                 have i₂ := b21e19 (M.op X2 X3) X0
                 grind)
              | (have i₁ := b21e34 X0 X1 X2 X3
                 have i₂ := b21e19 X0 (M.op X3 (M.op X2 X0))
                 grind)
              | exact superpose b21e19 b21e34
              | (have j1 := b21e19 (M.op X2 X3) X0
                 grind)
              | exact resolve b21e34 b21e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e216 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X3 X0)) = (M.op (M.op X3 X2) (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e34 X3 X2 X1 (M.op X3 X0)
                 have i₂ := b21e14 X0 X1 X3
                 grind)
              | exact superpose b21e14 b21e34
              | exact resolve b21e34 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e220 : ∀ X0 X1 : G, (M.op (M.op X1 X0) x) = (M.op (M.op x X1) (M.op x X0)) := by
              intro X0 X1
              first
              | (have i₁ := b21e34 x X1 X0 x
                 have i₂ := b21e54 X0
                 grind)
              | exact superpose b21e54 b21e34
              | exact resolve b21e34 b21e54
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e229 : ∀ X0 X1 : G, (M.op (M.op X1 X0) x) = (M.op (M.op x X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b21e220 X0 X1
                 have i₂ := b21e90 X0 (M.op x X1)
                 grind)
              | exact superpose b21e90 b21e220
              | exact resolve b21e220 b21e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e220
            have b21e240 : ∀ X0 X1 X2 : G, (M.op (M.op x X1) X2) = (M.op X0 (M.op X2 (M.op X1 (M.op x X0)))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e193 X0 X1 X2
                 have i₂ := b21e110 X0 (M.op X2 (M.op X1 (M.op x X0)))
                 grind)
              | exact superpose b21e110 b21e193
              | exact resolve b21e193 b21e110
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e193
            have b21e241 : ∀ X0 X1 X2 : G, (M.op (M.op x X1) X2) = (M.op X0 (M.op X2 (M.op X1 X0))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e240 X0 X1 X2
                 have i₂ := b21e90 X0 X1
                 grind)
              | exact superpose b21e90 b21e240
              | exact resolve b21e240 b21e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e240
            have b21e243 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op X1 (M.op X0 x)) := by
              intro X0 X1
              first
              | (have i₁ := b21e90 (M.op X0 x) X1
                 have i₂ := b21e54 X0
                 grind)
              | exact superpose b21e54 b21e90
              | exact resolve b21e90 b21e54
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e257 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X0)) = (M.op (M.op x X1) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e14 (M.op x X1) X2 X0
                 have i₂ := b21e90 X1 X0
                 grind)
              | exact superpose b21e90 b21e14
              | exact resolve b21e14 b21e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e259 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X0)) = (M.op (M.op X1 X2) x) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e34 X0 X1 X2 x
                 have i₂ := b21e90 (M.op X2 X0) (M.op X0 X1)
                 grind)
              | exact superpose b21e90 b21e34
              | exact resolve b21e34 b21e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e260 : (M.op (σ y) (σ x)) = (M.op (σ y) x) := by
              first
              | (have i₁ := b21e33 x
                 have i₂ := b21e90 (σ x) (σ y)
                 grind)
              | exact superpose b21e90 b21e33
              | exact resolve b21e33 b21e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e33
            have b21e262 : (M.op x y) = (M.op y x) := by
              first
              | (have i₁ := b21e32 x
                 have i₂ := b21e90 y x
                 grind)
              | exact superpose b21e90 b21e32
              | exact resolve b21e32 b21e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e32
            have b21e266 : ∀ X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) x) := by
              intro X1 X2
              first
              | (have i₁ := b21e259 x X1 X2
                 have i₂ := b21e14 X1 X2 x
                 grind)
              | exact superpose b21e14 b21e259
              | exact resolve b21e259 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e259
            have b21e267 : ∀ X1 X2 : G, (M.op X1 X2) = (M.op (M.op x X1) X2) := by
              intro X1 X2
              first
              | (have i₁ := b21e257 x X1 X2
                 have i₂ := b21e14 X1 X2 x
                 grind)
              | exact superpose b21e14 b21e257
              | exact resolve b21e257 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e257
            have b21e275 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 x)) := by
              intro X0 X1
              first
              | (have i₁ := b21e243 X0 X1
                 have i₂ := b21e90 X0 X1
                 grind)
              | exact superpose b21e90 b21e243
              | exact resolve b21e243 b21e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e243
            have b21e286 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X2 X4) X5)) = (M.op (M.op (M.op X0 (M.op X1 X2)) X3) (M.op X5 (M.op (M.op X4 X1) X0))) := by
              intro X0 X1 X2 X3 X4 X5
              first
              | (have i₁ := b21e37 X5 (M.op (M.op X4 X1) X0) X3 (M.op X2 X4)
                 have i₂ := b21e37 X2 X4 X0 X1
                 grind)
              | exact superpose b21e37 b21e37
              | exact resolve b21e37 b21e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e301 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op X0 x) (M.op X1 x)) := by
              intro X0 X1
              first
              | (have i₁ := b21e37 X1 x x X0
                 have i₂ := b21e53 X0
                 grind)
              | exact superpose b21e53 b21e37
              | exact resolve b21e37 b21e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e306 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op (M.op (M.op x X1) X3) X2) (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e37 X0 (M.op x X1) X2 X3
                 have i₂ := b21e90 X1 X0
                 grind)
              | exact superpose b21e90 b21e37
              | exact resolve b21e37 b21e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e307 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op (M.op X1 X4) X3) X2) (M.op X0 X1)) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b21e37 (M.op X4 X0) (M.op X1 X4) X2 X3
                 have i₂ := b21e14 X0 X1 X4
                 grind)
              | exact superpose b21e14 b21e37
              | exact resolve b21e37 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e317 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 x)) = (M.op (M.op (M.op (M.op X0 x) X2) X1) (M.op x X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e37 x (M.op X0 x) X1 X2
                 have i₂ := b21e54 X0
                 grind)
              | exact superpose b21e54 b21e37
              | exact resolve b21e37 b21e54
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e54
            have b21e318 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op (M.op x X1) X0) x) := by
              intro X0 X1
              first
              | (have i₁ := b21e37 x x X0 X1
                 have i₂ := b21e39
                 grind)
              | exact superpose b21e39 b21e37
              | exact resolve b21e37 b21e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e319 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op y X1) X0) x) := by
              intro X0 X1
              first
              | (have i₁ := b21e37 y y X0 X1
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e37
              | exact resolve b21e37 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e322 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) (M.op (M.op X4 X1) X0)) = (M.op (M.op X4 X3) (M.op X0 (M.op X1 X2))) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b21e34 X4 X3 X2 (M.op (M.op X4 X1) X0)
                 have i₂ := b21e37 X2 X4 X0 X1
                 grind)
              | exact superpose b21e37 b21e34
              | exact resolve b21e34 b21e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e339 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op x (M.op y X1)) X0) := by
              intro X0 X1
              first
              | (have i₁ := b21e319 X0 X1
                 have i₂ := b21e229 X0 (M.op y X1)
                 grind)
              | exact superpose b21e229 b21e319
              | exact resolve b21e319 b21e229
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e319
            have b21e340 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op x (M.op x X1)) X0) := by
              intro X0 X1
              first
              | (have i₁ := b21e318 X0 X1
                 have i₂ := b21e229 X0 (M.op x X1)
                 grind)
              | exact superpose b21e229 b21e318
              | exact resolve b21e318 b21e229
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e229 b21e318
            have b21e341 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 x)) = (M.op (M.op x (M.op (M.op X0 x) X2)) (M.op X0 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e317 X0 X1 X2
                 have i₂ := b21e216 X0 X1 (M.op (M.op X0 x) X2) x
                 grind)
              | (have i₁ := b21e317 X1 X2 X2
                 have i₂ := b21e216 x X1 X2 (M.op (M.op X1 x) X2)
                 grind)
              | exact superpose b21e216 b21e317
              | exact resolve b21e317 b21e216
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e317
            have b21e349 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X0))) = (M.op (M.op X2 X1) (M.op (M.op (M.op X1 X4) X3) X0)) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b21e307 X0 X1 X2 X3 X4
                 have i₂ := b21e216 X0 X1 X2 (M.op (M.op X1 X4) X3)
                 grind)
              | (have i₁ := b21e307 X3 X0 X1 X3 X4
                 have i₂ := b21e216 X0 X1 (M.op (M.op X0 X4) X3) X3
                 grind)
              | exact superpose b21e216 b21e307
              | exact resolve b21e307 b21e216
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e307
            have b21e350 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X2 X1) (M.op (M.op (M.op x X1) X3) X0)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e306 X0 X1 X2 X3
                 have i₂ := b21e216 X0 X1 X2 (M.op (M.op x X1) X3)
                 grind)
              | (have i₁ := b21e306 X3 X0 X1 X3
                 have i₂ := b21e216 X0 X1 (M.op (M.op x X0) X3) X3
                 grind)
              | exact superpose b21e216 b21e306
              | exact resolve b21e306 b21e216
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e306
            have b21e354 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op x (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b21e301 X0 X1
                 have i₂ := b21e110 X0 (M.op X1 x)
                 grind)
              | exact superpose b21e110 b21e301
              | exact resolve b21e301 b21e110
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e301
            have b21e363 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X2 X4) X5)) = (M.op (M.op X3 X0) (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X4 X1)) X5)) := by
              intro X0 X1 X2 X3 X4 X5
              first
              | (have i₁ := b21e286 X0 X1 X2 X3 X4 X5
                 have i₂ := b21e322 X5 (M.op X4 X1) X0 X3 (M.op X0 (M.op X1 X2))
                 grind)
              | exact superpose b21e322 b21e286
              | exact resolve b21e286 b21e322
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e286
            have b21e368 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 (M.op X1 y)) := by
              intro X0 X1
              first
              | (have i₁ := b21e339 X0 X1
                 have i₂ := b21e267 (M.op y X1) X0
                 grind)
              | (have i₁ := b21e339 x X1
                 have i₂ := b21e267 (M.op x (M.op y X1)) x
                 grind)
              | exact superpose b21e267 b21e339
              | exact resolve b21e339 b21e267
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e339
            have b21e369 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 (M.op X1 x)) := by
              intro X0 X1
              first
              | (have i₁ := b21e340 X0 X1
                 have i₂ := b21e267 (M.op x X1) X0
                 grind)
              | (have i₁ := b21e340 x X1
                 have i₂ := b21e267 (M.op x (M.op x X1)) x
                 grind)
              | exact superpose b21e267 b21e340
              | exact resolve b21e340 b21e267
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e340
            have b21e370 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 x)) = (M.op (M.op X0 x) (M.op X1 (M.op (M.op X0 x) X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e341 X0 X1 X2
                 have i₂ := b21e216 X1 (M.op (M.op X0 x) X2) x X0
                 grind)
              | (have i₁ := b21e341 X0 X1 X2
                 have i₂ := b21e216 X0 X1 (M.op (M.op X0 x) X2) x
                 grind)
              | exact superpose b21e216 b21e341
              | exact resolve b21e341 b21e216
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e341
            have b21e377 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X2 X1) (M.op (M.op X1 X3) X0)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e350 X0 X1 X2 X3
                 have i₂ := b21e267 X1 X3
                 grind)
              | (have i₁ := b21e350 X0 X1 X2 X2
                 have i₂ := b21e267 (M.op x X1) X2
                 grind)
              | exact superpose b21e267 b21e350
              | exact resolve b21e350 b21e267
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e267 b21e350
            have b21e378 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b21e354 X0 X1
                 have i₂ := b21e275 X1 X0
                 grind)
              | exact superpose b21e275 b21e354
              | exact resolve b21e354 b21e275
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e354
            have b21e385 : ∀ X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X2 X4) X5)) = (M.op X3 (M.op (M.op X4 X1) (M.op (M.op X1 X2) X5))) := by
              intro X1 X2 X3 X4 X5
              first
              | (have i₁ := b21e363 x X1 X2 X3 X4 X5
                 have i₂ := b21e349 X5 x X3 (M.op X4 X1) (M.op X1 X2)
                 grind)
              | exact superpose b21e349 b21e363
              | exact resolve b21e363 b21e349
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e349 b21e363
            have b21e389 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b21e369 X0 X1
                 have i₂ := b21e275 X1 X0
                 grind)
              | exact superpose b21e275 b21e369
              | exact resolve b21e369 b21e275
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e369
            have b21e390 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 x)) = (M.op X0 (M.op X1 (M.op (M.op X0 x) X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e370 X0 X1 X2
                 have i₂ := b21e110 X0 (M.op X1 (M.op (M.op X0 x) X2))
                 grind)
              | exact superpose b21e110 b21e370
              | exact resolve b21e370 b21e110
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e370
            have b21e397 : ∀ X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X2 X4) X5)) = (M.op X3 (M.op X4 (M.op X2 X5))) := by
              intro X2 X3 X4 X5
              first
              | (have i₁ := b21e385 x X2 X3 X4 X5
                 have i₂ := b21e377 X5 x X4 X2
                 grind)
              | exact superpose b21e377 b21e385
              | exact resolve b21e385 b21e377
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e385
            have b21e400 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 x)) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e390 X0 X1 X2
                 have i₂ := b21e110 X0 X2
                 grind)
              | exact superpose b21e110 b21e390
              | exact resolve b21e390 b21e110
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e390
            have b21e404 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e400 X0 X1 X2
                 have i₂ := b21e275 X2 X1
                 grind)
              | exact superpose b21e275 b21e400
              | exact resolve b21e400 b21e275
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e400
            have b21e407 : (σ y) ≠ (σ (M.op y x)) := by
              first
              | (have i₁ := b21e28
                 have i₂ := b21e262
                 grind)
              | exact superpose b21e262 b21e28
              | exact resolve b21e28 b21e262
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e28 b21e262
            have b21e556 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X1) (M.op X2 x)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e37 X2 x X0 X1
                 have i₂ := b21e389 X0 X1
                 grind)
              | exact superpose b21e389 b21e37
              | exact resolve b21e37 b21e389
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e557 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 x) X1) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 X1 X0 x
                 have i₂ := b21e389 (M.op X0 x) X1
                 grind)
              | exact superpose b21e389 b21e14
              | exact resolve b21e14 b21e389
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e559 : ∀ X0 : G, (M.op X0 x) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b21e53 X0
                 have i₂ := b21e389 x X0
                 grind)
              | exact superpose b21e389 b21e53
              | exact resolve b21e53 b21e389
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e53
            have b21e563 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) (M.op X2 (M.op x X1))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e14 X0 X2 (M.op x X1)
                 have i₂ := b21e389 X0 X1
                 grind)
              | exact superpose b21e389 b21e14
              | exact resolve b21e14 b21e389
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e566 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 (M.op x X1)))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e34 (M.op x X1) X0 X2 X3
                 have i₂ := b21e389 X0 X1
                 grind)
              | exact superpose b21e389 b21e34
              | exact resolve b21e34 b21e389
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e583 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X1))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e566 X0 X1 X2 X3
                 have i₂ := b21e90 X1 X2
                 grind)
              | exact superpose b21e90 b21e566
              | exact resolve b21e566 b21e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e566
            have b21e586 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e563 X0 X1 X2
                 have i₂ := b21e90 X1 X2
                 grind)
              | exact superpose b21e90 b21e563
              | exact resolve b21e563 b21e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e563
            have b21e589 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op X1 X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e556 X0 X1 X2
                 have i₂ := b21e275 X2 (M.op X0 X1)
                 grind)
              | exact superpose b21e275 b21e556
              | exact resolve b21e556 b21e275
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e556
            have b21e646 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X1 X0) X2) (M.op X0 X1)) ∨ (M.op X3 X0) = (k X0 X3) ∨ (M.op X0 X3) = X3 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e14 X2 X3 (M.op X1 X0)
                 have i₂ := b21e64 X3 X0 X1
                 grind)
              | exact superpose b21e64 b21e14
              | (have j1 := b21e64 X3 X0 X2
                 grind)
              | exact resolve b21e14 b21e64
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e64
            have b21e681 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X2 X1) (M.op (M.op X1 X0) X0)) ∨ (M.op X3 X0) = (k X0 X3) ∨ (M.op X0 X3) = X3 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e646 X0 X1 X2 X3
                 have i₂ := b21e216 X0 X1 X2 (M.op X1 X0)
                 grind)
              | (have i₁ := b21e646 X3 X0 X1 X3
                 have i₂ := b21e216 X0 X1 (M.op X0 X3) X3
                 grind)
              | exact superpose b21e216 b21e646
              | (have j0 := b21e646 X0 X1 X2 X3
                 grind)
              | exact resolve b21e646 b21e216
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e646
            have b21e717 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op X0 X0)) ∨ (M.op X3 X0) = (k X0 X3) ∨ (M.op X0 X3) = X3 := by
              intro X0 X2 X3
              first
              | (have i₁ := b21e681 X0 x X2 X3
                 have i₂ := b21e377 X0 x X2 X0
                 grind)
              | exact superpose b21e377 b21e681
              | (have j0 := b21e681 X0 x X2 X3
                 grind)
              | exact resolve b21e681 b21e377
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e681
            have b21e772 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op y X0)) := by
              intro X0
              first
              | (have i₁ := b21e35 X0
                 have i₂ := b21e559 (M.op y X0)
                 grind)
              | exact superpose b21e559 b21e35
              | exact resolve b21e35 b21e559
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e35 b21e559
            have b21e799 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b21e772 X0
                 have i₂ := b21e378 y X0
                 grind)
              | exact superpose b21e378 b21e772
              | exact resolve b21e772 b21e378
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e772
            have b21e985 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (σ (k x y)) := by
              intro X0
              first
              | (have i₁ := b21e50
                 have i₂ := b21e60 X0 y
                 grind)
              | exact superpose b21e60 b21e50
              | (have j1 := b21e60 X0 y
                 grind)
              | exact resolve b21e50 b21e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e1013 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b21e60 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e60
            have b21e1014 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b21e1013 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1013
            have b21e1122 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op X0 y) (M.op X1 (M.op X0 y))) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 x X1 (M.op X0 y)
                 have i₂ := b21e92 X0
                 grind)
              | exact superpose b21e92 b21e14
              | exact resolve b21e14 b21e92
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e92
            have b21e1136 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
              intro X0 X1
              first
              | (have i₁ := b21e1122 X0 X1
                 have i₂ := b21e583 X0 y X0 X1
                 grind)
              | exact superpose b21e583 b21e1122
              | exact resolve b21e1122 b21e583
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e583 b21e1122
            have b21e1142 : ∀ X0 X1 : G, (M.op x X1) = (M.op X0 (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b21e1136 X0 X1
                 have i₂ := b21e589 X0 X0 X1
                 grind)
              | exact superpose b21e589 b21e1136
              | exact resolve b21e1136 b21e589
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1136
            have b21e1253 : ∀ X0 X1 : G, (M.op x X1) = (M.op X0 (M.op X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 x X1 X0
                 have i₂ := b21e110 X0 (M.op X1 X0)
                 grind)
              | exact superpose b21e110 b21e14
              | exact resolve b21e14 b21e110
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e1654 : (σ y) = (M.op x (σ y)) := by
              first
              | (have i₁ := b21e378 (σ x) (σ y)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e378
              | exact resolve b21e378 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e1680 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 x))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e34 x (M.op X0 X1) X2 X3
                 have i₂ := b21e378 X0 X1
                 grind)
              | exact superpose b21e378 b21e34
              | exact resolve b21e34 b21e378
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e34
            have b21e1692 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op X0 (M.op X1 (M.op X3 (M.op X2 x)))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e1680 X0 X1 X2 X3
                 have i₂ := b21e589 X0 X1 (M.op X3 (M.op X2 x))
                 grind)
              | exact superpose b21e589 b21e1680
              | exact resolve b21e1680 b21e589
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1680
            have b21e1697 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op X0 (M.op X1 (M.op X3 X2))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e1692 X0 X1 X2 X3
                 have i₂ := b21e275 X2 X3
                 grind)
              | exact superpose b21e275 b21e1692
              | exact resolve b21e1692 b21e275
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e275 b21e1692
            have b21e1701 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op X0 (M.op X1 (M.op X3 X2))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e1697 X0 X1 X2 X3
                 have i₂ := b21e589 (M.op X0 X1) X2 X3
                 grind)
              | exact superpose b21e589 b21e1697
              | exact resolve b21e1697 b21e589
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1697
            have b21e1704 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X3 X2))) = (M.op X0 (M.op X1 (M.op X2 X3))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e1701 X0 X1 X3 X2
                 have i₂ := b21e589 X0 X1 (M.op X3 X2)
                 grind)
              | exact superpose b21e589 b21e1701
              | exact resolve b21e1701 b21e589
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1701
            have b21e1741 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b21e389 X0 (σ y)
                 have i₂ := b21e1654
                 grind)
              | exact superpose b21e1654 b21e389
              | exact resolve b21e389 b21e1654
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e1817 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X0 X1) X1) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 x X0 X1
                 have i₂ := b21e557 X1 (M.op X0 X1)
                 grind)
              | exact superpose b21e557 b21e14
              | exact resolve b21e14 b21e557
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e1870 : ∀ X0 X1 : G, (M.op x X0) = (M.op X0 (M.op X1 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b21e1817 X0 X1
                 have i₂ := b21e589 X0 X1 X1
                 grind)
              | exact superpose b21e589 b21e1817
              | exact resolve b21e1817 b21e589
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1817
            have b21e1955 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b21e389 X0 (σ x)
                 have i₂ := b21e156 x X0
                 grind)
              | exact superpose b21e156 b21e389
              | exact resolve b21e389 b21e156
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e1958 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op X0 (M.op X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 (σ x) X1 X0
                 have i₂ := b21e156 X0 (M.op X1 X0)
                 grind)
              | exact superpose b21e156 b21e14
              | exact resolve b21e14 b21e156
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e1961 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b21e36 (σ x)
                 have i₂ := b21e156 (σ y) (σ y)
                 grind)
              | exact superpose b21e156 b21e36
              | exact resolve b21e36 b21e156
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e36 b21e156
            have b21e2014 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b21e1961
                 have i₂ := b21e50
                 grind)
              | exact superpose b21e50 b21e1961
              | exact resolve b21e1961 b21e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1961
            have b21e2017 : ∀ X1 : G, (M.op x X1) = (M.op (σ x) X1) := by
              intro X1
              first
              | (have i₁ := b21e1958 x X1
                 have i₂ := b21e1253 x X1
                 grind)
              | exact superpose b21e1253 b21e1958
              | exact resolve b21e1958 b21e1253
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1958
            have b21e2056 : (σ (k x y)) = (M.op x (σ x)) := by
              first
              | (have i₁ := b21e2014
                 have i₂ := b21e1955 (σ x)
                 grind)
              | exact superpose b21e1955 b21e2014
              | exact resolve b21e2014 b21e1955
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2014
            have b21e2084 : (M.op x x) = (σ (k x y)) := by
              first
              | (have i₁ := b21e2056
                 have i₂ := b21e1955 x
                 grind)
              | exact superpose b21e1955 b21e2056
              | exact resolve b21e2056 b21e1955
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2056
            have b21e2103 : x = (σ (k x y)) := by
              first
              | (have i₁ := b21e2084
                 have i₂ := b21e39
                 grind)
              | exact superpose b21e39 b21e2084
              | exact resolve b21e2084 b21e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2084
            have b21e2136 : x = (σ (M.op y x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b21e2103
                 have i₂ := b21e19 x y
                 grind)
              | exact superpose b21e19 b21e2103
              | (have j1 := b21e19 x y
                 grind)
              | exact resolve b21e2103 b21e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e2137 : (k x y) = (τ x) := by
              first
              | (have i₁ := b21e15 (k x y)
                 have i₂ := b21e2103
                 grind)
              | exact superpose b21e2103 b21e15
              | exact resolve b21e15 b21e2103
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e2138 : ∀ X0 : G, (σ (k (k x y) X0)) = (k x (σ X0)) := by
              intro X0
              first
              | (have i₁ := b21e20 (k x y) X0
                 have i₂ := b21e2103
                 grind)
              | exact superpose b21e2103 b21e20
              | exact resolve b21e20 b21e2103
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e2152 : x = (σ (M.op y x)) ∨ y = (M.op x y) := by
              first
              | (have r₁ := b21e2136
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e2136 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2136
            have b21e2161 : x = (σ (M.op y x)) := by
              first
              | (have r₁ := b21e2152
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e2152 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2152
            have b21e2223 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op y X1))) = (M.op (M.op (M.op X0 X3) X2) (M.op X0 (M.op X1 y))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e37 (M.op y X1) X0 X2 X3
                 have i₂ := b21e368 X0 X1
                 grind)
              | (have i₁ := b21e37 X0 (M.op X1 y) X2 X3
                 have i₂ := b21e368 X0 X1
                 grind)
              | exact superpose b21e368 b21e37
              | exact resolve b21e37 b21e368
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e37 b21e368
            have b21e2306 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op y X1))) = (M.op (M.op X2 y) (M.op (M.op (M.op X0 X3) X1) X0)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e2223 X0 X1 X2 X3
                 have i₂ := b21e322 X0 X1 y X2 (M.op X0 X3)
                 grind)
              | exact superpose b21e322 b21e2223
              | exact resolve b21e2223 b21e322
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e322 b21e2223
            have b21e2375 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op y X1))) = (M.op X2 (M.op y (M.op (M.op (M.op X0 X3) X1) X0))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e2306 X0 X1 X2 X3
                 have i₂ := b21e589 X2 y (M.op (M.op (M.op X0 X3) X1) X0)
                 grind)
              | exact superpose b21e589 b21e2306
              | exact resolve b21e2306 b21e589
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2306
            have b21e2427 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op y X1))) = (M.op X2 (M.op y (M.op X0 (M.op (M.op X0 X3) X1)))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e2375 X0 X1 X2 X3
                 have i₂ := b21e1704 X2 y X0 (M.op (M.op X0 X3) X1)
                 grind)
              | (have i₁ := b21e2375 X0 X1 X2 X3
                 have i₂ := b21e1704 X2 y (M.op (M.op X0 X3) X1) X0
                 grind)
              | exact superpose b21e1704 b21e2375
              | exact resolve b21e2375 b21e1704
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2375
            have b21e2457 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op y X1))) = (M.op X2 (M.op y (M.op X0 (M.op X3 (M.op X0 X1))))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e2427 X0 X1 X2 X3
                 have i₂ := b21e397 X0 X0 X3 X1
                 grind)
              | (have i₁ := b21e2427 X3 (M.op X2 x) X2 X3
                 have i₂ := b21e397 X2 X3 (M.op X3 X3) x
                 grind)
              | exact superpose b21e397 b21e2427
              | exact resolve b21e2427 b21e397
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2427
            have b21e2474 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op y X1))) = (M.op X2 (M.op y (M.op X3 X1))) := by
              intro X1 X2 X3
              first
              | (have i₁ := b21e2457 x X1 X2 X3
                 have i₂ := b21e404 x X3 X1
                 grind)
              | exact superpose b21e404 b21e2457
              | exact resolve b21e2457 b21e404
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e404 b21e2457
            have b21e2507 : (M.op y x) = (τ x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b21e19 x y
                 have i₂ := b21e2137
                 grind)
              | exact superpose b21e2137 b21e19
              | (have j0 := b21e19 x y
                 grind)
              | exact resolve b21e19 b21e2137
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2137
            have b21e2508 : (M.op y x) = (τ x) ∨ y = (M.op x y) := by
              first
              | (have r₁ := b21e2507
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e2507 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2507
            have b21e2517 : (M.op y x) = (τ x) := by
              first
              | (have r₁ := b21e2508
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e2508 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2508
            have b21e2754 : x ≠ (σ y) := by
              first
              | (have i₁ := b21e407
                 have i₂ := b21e2161
                 grind)
              | exact superpose b21e2161 b21e407
              | exact resolve b21e407 b21e2161
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e407 b21e2161
            have b21e3329 : ∀ X0 : G, (M.op X0 y) = (M.op (τ x) X0) := by
              intro X0
              first
              | (have i₁ := b21e557 y X0
                 have i₂ := b21e2517
                 grind)
              | exact superpose b21e2517 b21e557
              | exact resolve b21e557 b21e2517
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e557
            have b21e3330 : ∀ X0 : G, (M.op y X0) = (M.op (τ x) X0) := by
              intro X0
              first
              | (have i₁ := b21e110 y X0
                 have i₂ := b21e2517
                 grind)
              | exact superpose b21e2517 b21e110
              | exact resolve b21e110 b21e2517
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e110 b21e2517
            have b21e3392 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ (k x y)) (σ (k x y))) ∨ (M.op (σ y) (σ y)) = (k (σ (k x y)) (σ y)) := by
              first
              | (have i₁ := b21e18 (σ (k x y)) (σ y)
                 have i₂ := b21e170
                 grind)
              | exact superpose b21e170 b21e18
              | (have j0 := b21e18 (σ (k x y)) (σ y)
                 grind)
              | exact resolve b21e18 b21e170
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e170
            have b21e3410 : (σ y) ≠ (M.op (σ y) x) ∨ (σ y) = (M.op (σ (k x y)) (σ (k x y))) ∨ (M.op (σ y) (σ y)) = (k (σ (k x y)) (σ y)) := by
              first
              | (have i₁ := b21e3392
                 have i₂ := b21e260
                 grind)
              | exact superpose b21e260 b21e3392
              | exact resolve b21e3392 b21e260
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e260 b21e3392
            have b21e3426 : (σ y) ≠ (M.op x (σ y)) ∨ (σ y) = (M.op (σ (k x y)) (σ (k x y))) ∨ (M.op (σ y) (σ y)) = (k (σ (k x y)) (σ y)) := by
              first
              | (have i₁ := b21e3410
                 have i₂ := b21e1741 x
                 grind)
              | exact superpose b21e1741 b21e3410
              | exact resolve b21e3410 b21e1741
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1741 b21e3410
            have b21e3442 : (σ y) = (M.op (σ (k x y)) (σ (k x y))) ∨ (M.op (σ y) (σ y)) = (k (σ (k x y)) (σ y)) := by
              first
              | (have r₁ := b21e3426
                 have r₂ := b21e1654
                 grind)
              | exact resolve b21e3426 b21e1654
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e3426
            have b21e3455 : (σ y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (k (σ (k x y)) (σ y)) := by
              first
              | (have i₁ := b21e3442
                 have i₂ := b21e2103
                 grind)
              | exact superpose b21e2103 b21e3442
              | exact resolve b21e3442 b21e2103
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e3442
            have b21e3464 : x = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ (k x y)) (σ y)) := by
              first
              | (have i₁ := b21e3455
                 have i₂ := b21e39
                 grind)
              | exact superpose b21e39 b21e3455
              | exact resolve b21e3455 b21e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e3455
            have b21e3471 : (M.op (σ y) (σ y)) = (k (σ (k x y)) (σ y)) := by
              first
              | (have r₁ := b21e3464
                 have r₂ := b21e2754
                 grind)
              | exact resolve b21e3464 b21e2754
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e3464
            have b21e3478 : (M.op (σ y) (σ y)) = (σ (k (k x y) y)) := by
              first
              | (have i₁ := b21e3471
                 have i₂ := b21e20 (k x y) y
                 grind)
              | exact superpose b21e20 b21e3471
              | exact resolve b21e3471 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e3471
            have b21e3481 : (M.op (σ y) (σ y)) = (k x (σ y)) := by
              first
              | (have i₁ := b21e3478
                 have i₂ := b21e2138 y
                 grind)
              | exact superpose b21e2138 b21e3478
              | exact resolve b21e3478 b21e2138
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2138 b21e3478
            have b21e3483 : (σ (k x y)) = (k x (σ y)) := by
              first
              | (have i₁ := b21e3481
                 have i₂ := b21e50
                 grind)
              | exact superpose b21e50 b21e3481
              | exact resolve b21e3481 b21e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e50 b21e3481
            have b21e3485 : x = (k x (σ y)) := by
              first
              | (have i₁ := b21e3483
                 have i₂ := b21e2103
                 grind)
              | exact superpose b21e2103 b21e3483
              | exact resolve b21e3483 b21e2103
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e3483
            have b21e3537 : ∀ X0 X1 X2 : G, (M.op X2 x) = (M.op (M.op (M.op X1 (M.op X0 y)) X2) (M.op (M.op y X0) X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e14 X2 x (M.op X1 (M.op X0 y))
                 have i₂ := b21e201 X0 X1
                 grind)
              | exact superpose b21e201 b21e14
              | exact resolve b21e14 b21e201
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e201
            have b21e3555 : ∀ X0 X1 X2 : G, (M.op X2 x) = (M.op (M.op X2 X1) (M.op (M.op X1 (M.op X0 y)) (M.op y X0))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e3537 X0 X1 X2
                 have i₂ := b21e216 (M.op y X0) X1 X2 (M.op X1 (M.op X0 y))
                 grind)
              | (have i₁ := b21e3537 X0 X0 X1
                 have i₂ := b21e216 X0 X1 (M.op X0 (M.op X0 y)) (M.op y X0)
                 grind)
              | exact superpose b21e216 b21e3537
              | exact resolve b21e3537 b21e216
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e216 b21e3537
            have b21e3590 : ∀ X0 X2 : G, (M.op X2 x) = (M.op X2 (M.op (M.op X0 y) (M.op y X0))) := by
              intro X0 X2
              first
              | (have i₁ := b21e3555 X0 x X2
                 have i₂ := b21e377 (M.op y X0) x X2 (M.op X0 y)
                 grind)
              | exact superpose b21e377 b21e3555
              | exact resolve b21e3555 b21e377
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e377 b21e3555
            have b21e3619 : ∀ X0 X2 : G, (M.op X2 x) = (M.op X2 (M.op y (M.op (M.op X0 y) X0))) := by
              intro X0 X2
              first
              | (have i₁ := b21e3590 X0 X2
                 have i₂ := b21e2474 X0 X2 (M.op X0 y)
                 grind)
              | exact superpose b21e2474 b21e3590
              | exact resolve b21e3590 b21e2474
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2474 b21e3590
            have b21e3641 : ∀ X0 X2 : G, (M.op X2 x) = (M.op X2 (M.op y (M.op X0 (M.op X0 y)))) := by
              intro X0 X2
              first
              | (have i₁ := b21e3619 X0 X2
                 have i₂ := b21e1704 X2 y X0 (M.op X0 y)
                 grind)
              | (have i₁ := b21e3619 X0 X2
                 have i₂ := b21e1704 X2 y (M.op X0 y) X0
                 grind)
              | exact superpose b21e1704 b21e3619
              | exact resolve b21e3619 b21e1704
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1704 b21e3619
            have b21e3660 : ∀ X0 X2 : G, (M.op X2 x) = (M.op X2 (M.op (M.op x X0) X0)) := by
              intro X0 X2
              first
              | (have i₁ := b21e3641 X0 X2
                 have i₂ := b21e241 y X0 X0
                 grind)
              | exact superpose b21e241 b21e3641
              | exact resolve b21e3641 b21e241
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e241 b21e3641
            have b21e3671 : ∀ X0 X2 : G, (M.op X2 x) = (M.op X2 (M.op X0 (M.op x X0))) := by
              intro X0 X2
              first
              | (have i₁ := b21e3660 X0 X2
                 have i₂ := b21e397 x X2 X0 X0
                 grind)
              | (have i₁ := b21e3660 (M.op X2 x) x
                 have i₂ := b21e397 X2 x (M.op x (M.op X2 x)) x
                 grind)
              | exact superpose b21e397 b21e3660
              | exact resolve b21e3660 b21e397
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e397 b21e3660
            have b21e3679 : ∀ X0 X2 : G, (M.op X2 x) = (M.op X2 (M.op X0 X0)) := by
              intro X0 X2
              first
              | (have i₁ := b21e3671 X0 X2
                 have i₂ := b21e90 X0 X0
                 grind)
              | exact superpose b21e90 b21e3671
              | exact resolve b21e3671 b21e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e3671
            have b21e3691 : (τ x) = (k (τ x) y) := by
              first
              | (have i₁ := b21e82 x y
                 have i₂ := b21e3485
                 grind)
              | exact superpose b21e3485 b21e82
              | exact resolve b21e82 b21e3485
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e82 b21e3485
            have b21e12188 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b21e1014 x
                 have i₂ := b21e52
                 grind)
              | exact superpose b21e52 b21e1014
              | (have j0 := b21e1014 x
                 grind)
              | exact resolve b21e1014 b21e52
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e52 b21e1014
            have b21e12194 : (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b21e12188
            have b21e12200 : (σ x) = (M.op x (σ x)) := by
              first
              | (have i₁ := b21e12194
                 have i₂ := b21e2017 (σ x)
                 grind)
              | exact superpose b21e2017 b21e12194
              | exact resolve b21e12194 b21e2017
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2017 b21e12194
            have b21e12203 : (σ x) = (M.op x x) := by
              first
              | (have i₁ := b21e12200
                 have i₂ := b21e1955 x
                 grind)
              | exact superpose b21e1955 b21e12200
              | exact resolve b21e12200 b21e1955
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1955 b21e12200
            have b21e12204 : x = (σ x) := by
              first
              | (have i₁ := b21e12203
                 have i₂ := b21e39
                 grind)
              | exact superpose b21e39 b21e12203
              | exact resolve b21e12203 b21e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e12203
            have b21e12214 : x = (τ x) := by
              first
              | (have i₁ := b21e15 x
                 have i₂ := b21e12204
                 grind)
              | exact superpose b21e12204 b21e15
              | exact resolve b21e15 b21e12204
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e12231 : ∀ X0 : G, (τ (k x X0)) = (k x (τ X0)) := by
              intro X0
              first
              | (have i₁ := b21e100 x X0
                 have i₂ := b21e12204
                 grind)
              | exact superpose b21e12204 b21e100
              | exact resolve b21e100 b21e12204
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e12688 : ∀ X0 : G, (M.op X0 y) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b21e3329 X0
                 have i₂ := b21e12214
                 grind)
              | exact superpose b21e12214 b21e3329
              | exact resolve b21e3329 b21e12214
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e3329
            have b21e12689 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b21e3330 X0
                 have i₂ := b21e12214
                 grind)
              | exact superpose b21e12214 b21e3330
              | exact resolve b21e3330 b21e12214
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e3330
            have b21e12692 : x = (k x y) := by
              first
              | (have i₁ := b21e3691
                 have i₂ := b21e12214
                 grind)
              | exact superpose b21e12214 b21e3691
              | exact resolve b21e3691 b21e12214
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e3691
            have b21e13814 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op y X1) (M.op x X0)) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 X1 X0 y
                 have i₂ := b21e12688 X0
                 grind)
              | exact superpose b21e12688 b21e14
              | exact resolve b21e14 b21e12688
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e12688
            have b21e13985 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op X1 (M.op x X0))) := by
              intro X0 X1
              first
              | (have i₁ := b21e13814 X0 X1
                 have i₂ := b21e589 y X1 (M.op x X0)
                 grind)
              | exact superpose b21e589 b21e13814
              | exact resolve b21e13814 b21e589
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e13814
            have b21e14063 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b21e13985 X0 X1
                 have i₂ := b21e90 X0 X1
                 grind)
              | exact superpose b21e90 b21e13985
              | exact resolve b21e13985 b21e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e90 b21e13985
            have b21e14736 : (σ y) = (M.op y (σ y)) := by
              first
              | (have i₁ := b21e1654
                 have i₂ := b21e12689 (σ y)
                 grind)
              | exact superpose b21e12689 b21e1654
              | exact resolve b21e1654 b21e12689
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1654
            have b21e23322 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x X1) x) := by
              intro X0 X1
              first
              | (have i₁ := b21e3679 X0 (M.op x X1)
                 have i₂ := b21e389 (M.op X0 X0) X1
                 grind)
              | exact superpose b21e389 b21e3679
              | exact resolve b21e3679 b21e389
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e389
            have b21e23432 : ∀ X0 : G, (M.op X0 X0) = (M.op x x) := by
              intro X0
              first
              | (have i₁ := b21e378 X0 X0
                 have i₂ := b21e3679 X0 x
                 grind)
              | exact superpose b21e3679 b21e378
              | exact resolve b21e378 b21e3679
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e378 b21e3679
            have b21e23471 : ∀ X0 : G, (M.op X0 X0) = x := by
              intro X0
              first
              | (have i₁ := b21e23432 X0
                 have i₂ := b21e39
                 grind)
              | exact superpose b21e39 b21e23432
              | exact resolve b21e23432 b21e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e39 b21e23432
            have b21e23577 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
              intro X0 X1
              first
              | (have i₁ := b21e23322 X0 X1
                 have i₂ := b21e266 x X1
                 grind)
              | exact superpose b21e266 b21e23322
              | exact resolve b21e23322 b21e266
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e266 b21e23322
            have b21e23734 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) := by
              intro X0 X1
              first
              | (have i₁ := b21e23577 X0 X1
                 have i₂ := b21e12689 X1
                 grind)
              | exact superpose b21e12689 b21e23577
              | exact resolve b21e23577 b21e12689
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e23577
            have b21e23837 : ∀ X0 X1 : G, (M.op y X1) = (M.op X0 (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b21e23734 X0 X1
                 have i₂ := b21e589 X0 X0 X1
                 grind)
              | exact superpose b21e589 b21e23734
              | exact resolve b21e23734 b21e589
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e23734
            have b21e24243 : ∀ X0 X1 : G, x = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b21e19 X0 X1
                 have i₂ := b21e23471 X0
                 grind)
              | exact superpose b21e23471 b21e19
              | (have j0 := b21e19 X0 X1
                 grind)
              | exact resolve b21e19 b21e23471
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e32348 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 X1 (M.op X0 X1) X0
                 have i₂ := b21e23837 (M.op X0 X1) X0
                 grind)
              | exact superpose b21e23837 b21e14
              | exact resolve b21e14 b21e23837
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e23837
            have b21e83660 : (τ x) = (k x (τ y)) := by
              first
              | (have i₁ := b21e12231 y
                 have i₂ := b21e12692
                 grind)
              | exact superpose b21e12692 b21e12231
              | exact resolve b21e12231 b21e12692
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e12231 b21e12692
            have b21e83697 : x = (k x (τ y)) := by
              first
              | (have i₁ := b21e83660
                 have i₂ := b21e12214
                 grind)
              | exact superpose b21e12214 b21e83660
              | exact resolve b21e83660 b21e12214
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e12214 b21e83660
            have b21e86484 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b21e717 X0 x X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e717
            have b21e86486 : ∀ X0 X1 : G, (M.op x X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b21e86484 X0 X1
                 have i₂ := b21e1253 X0 X0
                 grind)
              | exact superpose b21e1253 b21e86484
              | (have j0 := b21e86484 X0 X1
                 grind)
              | (have r₁ := b21e86484 x (M.op X0 (M.op (M.op x x) X0))
                 have r₂ := b21e1253 X0 (M.op x x)
                 grind)
              | (have r₁ := b21e86484 X1 (M.op x X1)
                 have r₂ := b21e1253 X1 X1
                 grind)
              | exact resolve b21e86484 b21e1253
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1253 b21e86484
            have b21e87162 : ∀ X0 X1 : G, (M.op y X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b21e86486 X0 X1
                 have i₂ := b21e12689 X0
                 grind)
              | exact superpose b21e12689 b21e86486
              | (have j0 := b21e86486 X0 X1
                 grind)
              | (have r₁ := b21e86486 X0 (M.op y X0)
                 have r₂ := b21e12689 X0
                 grind)
              | exact resolve b21e86486 b21e12689
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e86486
            have b21e141054 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op y y) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k y (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b21e18 y (M.op X0 X1)
                 have i₂ := b21e14063 X1 X0
                 grind)
              | exact superpose b21e14063 b21e18
              | (have j0 := b21e18 y (M.op X0 X1)
                 grind)
              | (have r₁ := b21e18 y (M.op X1 X0)
                 have r₂ := b21e14063 X0 X1
                 grind)
              | exact resolve b21e18 b21e14063
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e14063
            have b21e141119 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y y) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k y (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have j0 := b21e141054 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e141054
            have b21e141167 : ∀ X0 X1 : G, (M.op X0 X1) = x ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k y (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b21e141119 X0 X1
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e141119
              | (have j0 := b21e141119 X0 X1
                 grind)
              | exact resolve b21e141119 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e141119
            have b21e141282 : ∀ X0 X1 : G, (M.op X0 X0) = (k y (M.op X0 X1)) ∨ (M.op X0 X1) = x := by
              intro X0 X1
              first
              | (have i₁ := b21e141167 X0 X1
                 have i₂ := b21e586 X0 X1 X0
                 grind)
              | exact superpose b21e586 b21e141167
              | (have j0 := b21e141167 X0 X1
                 grind)
              | exact resolve b21e141167 b21e586
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e586 b21e141167
            have b21e141369 : ∀ X0 X1 : G, x = (k y (M.op X0 X1)) ∨ (M.op X0 X1) = x := by
              intro X0 X1
              first
              | (have i₁ := b21e141282 X0 X1
                 have i₂ := b21e23471 X0
                 grind)
              | exact superpose b21e23471 b21e141282
              | (have j0 := b21e141282 X0 X1
                 grind)
              | exact resolve b21e141282 b21e23471
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e141282
            have b21e210729 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op y (σ y)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ (k x y)) := by
              intro X0
              first
              | (have i₁ := b21e32348 (σ y) (σ X0)
                 have i₂ := b21e985 X0
                 grind)
              | exact superpose b21e985 b21e32348
              | (have j1 := b21e985 X0
                 grind)
              | exact resolve b21e32348 b21e985
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e985 b21e32348
            have b21e210740 : ∀ X0 : G, (σ y) = (M.op (σ X0) (σ X0)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ (k x y)) := by
              intro X0
              first
              | (have i₁ := b21e210729 X0
                 have i₂ := b21e14736
                 grind)
              | exact superpose b21e14736 b21e210729
              | (have j0 := b21e210729 X0
                 grind)
              | exact resolve b21e210729 b21e14736
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e210729
            have b21e210932 : ∀ X0 : G, x = (σ y) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ (k x y)) := by
              intro X0
              first
              | (have i₁ := b21e210740 X0
                 have i₂ := b21e23471 (σ X0)
                 grind)
              | exact superpose b21e23471 b21e210740
              | (have j0 := b21e210740 X0
                 grind)
              | exact resolve b21e210740 b21e23471
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e210740
            have b21e211078 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ (k x y)) := by
              intro X0
              first
              | (have j0 := b21e210932 X0
                 grind)
              | (have r₁ := b21e210932 X0
                 have r₂ := b21e2754
                 grind)
              | exact resolve b21e210932 b21e2754
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e210932
            have b21e211194 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = x := by
              intro X0
              first
              | (have i₁ := b21e211078 X0
                 have i₂ := b21e2103
                 grind)
              | exact superpose b21e2103 b21e211078
              | (have j0 := b21e211078 X0
                 grind)
              | exact resolve b21e211078 b21e2103
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2103 b21e211078
            have b21e338397 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X1 ∨ (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b21e215 X1 X1 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e215
            have b21e338410 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b21e338397 X0 X1
                 have j1 := b21e19 (M.op X0 X0) X1
                 grind)
              | (have r₁ := b21e338397 X0 (k (M.op X0 X0) (M.op X0 X0))
                 have r₂ := b21e19 (M.op X0 X0) (M.op X0 X0)
                 grind)
              | (have r₁ := b21e338397 X0 X1
                 have r₂ := b21e19 (M.op X0 X0) X1
                 grind)
              | (have r₁ := b21e338397 X0 (M.op X0 X0)
                 have r₂ := b21e19 X0 (M.op (M.op X0 X0) (M.op X0 X0))
                 grind)
              | exact resolve b21e338397 b21e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e338397
            have b21e338509 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op x X1) ∨ (M.op (M.op X0 X0) X1) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b21e338410 X0 X1
                 have i₂ := b21e1870 X1 X0
                 grind)
              | exact superpose b21e1870 b21e338410
              | (have j0 := b21e338410 X0 X1
                 grind)
              | exact resolve b21e338410 b21e1870
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1870 b21e338410
            have b21e338600 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op y X1) ∨ (M.op (M.op X0 X0) X1) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b21e338509 X0 X1
                 have i₂ := b21e12689 X1
                 grind)
              | exact superpose b21e12689 b21e338509
              | (have j0 := b21e338509 X0 X1
                 grind)
              | exact resolve b21e338509 b21e12689
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e338509
            have b21e338644 : ∀ X0 X1 : G, (M.op y X1) = (k x X1) ∨ (M.op (M.op X0 X0) X1) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b21e338600 X0 X1
                 have i₂ := b21e23471 X0
                 grind)
              | exact superpose b21e23471 b21e338600
              | (have j0 := b21e338600 X0 X1
                 grind)
              | exact resolve b21e338600 b21e23471
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e338600
            have b21e338662 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 ∨ (M.op y X1) = (k x X1) := by
              intro X0 X1
              first
              | (have i₁ := b21e338644 X0 X1
                 have i₂ := b21e589 X0 X0 X1
                 grind)
              | exact superpose b21e589 b21e338644
              | (have j0 := b21e338644 X0 X1
                 grind)
              | exact resolve b21e338644 b21e589
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e589 b21e338644
            have b21e338674 : ∀ X1 : G, (M.op x X1) = X1 ∨ (M.op y X1) = (k x X1) := by
              intro X1
              first
              | (have i₁ := b21e338662 x X1
                 have i₂ := b21e1142 x X1
                 grind)
              | exact superpose b21e1142 b21e338662
              | (have j0 := b21e338662 x X1
                 grind)
              | exact resolve b21e338662 b21e1142
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1142 b21e338662
            have b21e338679 : ∀ X1 : G, (M.op y X1) = (k x X1) ∨ (M.op y X1) = X1 := by
              intro X1
              first
              | (have i₁ := b21e338674 X1
                 have i₂ := b21e12689 X1
                 grind)
              | exact superpose b21e12689 b21e338674
              | (have j0 := b21e338674 X1
                 grind)
              | exact resolve b21e338674 b21e12689
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e12689 b21e338674
            have b21e390614 : (τ y) = (M.op y (τ y)) ∨ x = (M.op y (τ y)) := by
              first
              | (have i₁ := b21e83697
                 have i₂ := b21e338679 (τ y)
                 grind)
              | exact superpose b21e338679 b21e83697
              | (have j1 := b21e338679 (τ y)
                 grind)
              | exact resolve b21e83697 b21e338679
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e83697 b21e338679
            have b21e644223 : x = (k y (τ y)) ∨ x = (τ y) ∨ x = (M.op y (τ y)) := by
              first
              | (have i₁ := b21e141369 y (τ y)
                 have i₂ := b21e390614
                 grind)
              | exact superpose b21e390614 b21e141369
              | (have j0 := b21e141369 y (τ y)
                 grind)
              | exact resolve b21e141369 b21e390614
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e141369
            have b21e644228 : x ≠ (τ y) ∨ x = (M.op y (τ y)) := by grind
            clear b21e390614
            have b21e644231 : x = (k y (τ y)) ∨ x = (M.op y (τ y)) := by
              first
              | (have r₁ := b21e644223
                 have r₂ := b21e644228
                 grind)
              | exact resolve b21e644223 b21e644228
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e644223 b21e644228
            have b21e649268 : (σ x) = (k (σ y) y) ∨ x = (M.op y (τ y)) := by
              first
              | (have i₁ := b21e31 y y
                 have i₂ := b21e644231
                 grind)
              | exact superpose b21e644231 b21e31
              | exact resolve b21e31 b21e644231
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e644231
            have b21e649271 : x = (k (σ y) y) ∨ x = (M.op y (τ y)) := by
              first
              | (have i₁ := b21e649268
                 have i₂ := b21e12204
                 grind)
              | exact superpose b21e12204 b21e649268
              | exact resolve b21e649268 b21e12204
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e649268
            have b21e652923 : ∀ X0 : G, x ≠ X0 ∨ (M.op X0 y) = (k y X0) ∨ (M.op y X0) = X0 := by
              intro X0
              first
              | (have i₁ := b21e87162 y X0
                 have i₂ := b21e23471 y
                 grind)
              | exact superpose b21e23471 b21e87162
              | (have j0 := b21e87162 y X0
                 grind)
              | (have r₁ := b21e87162 y x
                 have r₂ := b21e23471 y
                 grind)
              | exact resolve b21e87162 b21e23471
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e23471 b21e87162
            have b21e652972 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ (M.op y X0) = X0 := by
              intro X0
              first
              | (have j0 := b21e652923 X0
                 have j1 := b21e24243 y X0
                 grind)
              | (have r₁ := b21e652923 x
                 have r₂ := b21e24243 X0 x
                 grind)
              | (have r₁ := b21e652923 x
                 have r₂ := b21e24243 X0 x
                 grind)
              | (have r₁ := b21e652923 (M.op X0 x)
                 have r₂ := b21e24243 X0 x
                 grind)
              | exact resolve b21e652923 b21e24243
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e24243 b21e652923
            have b21e1013325 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (k y (τ X0))) ∨ x = X0 := by
              intro X0
              first
              | (have i₁ := b21e211194 (τ X0)
                 have i₂ := b21e16 X0
                 grind)
              | exact superpose b21e16 b21e211194
              | exact resolve b21e211194 b21e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e211194
            have b21e1013493 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = X0 := by
              intro X0
              first
              | (have i₁ := b21e1013325 X0
                 have i₂ := b21e31 X0 y
                 grind)
              | exact superpose b21e31 b21e1013325
              | (have j0 := b21e1013325 X0
                 grind)
              | exact resolve b21e1013325 b21e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e31 b21e1013325
            have b21e1017964 : x = (M.op y (σ y)) ∨ x = (M.op y (τ y)) ∨ x = y := by
              first
              | (have i₁ := b21e649271
                 have i₂ := b21e1013493 y
                 grind)
              | exact superpose b21e1013493 b21e649271
              | (have j1 := b21e1013493 (M.op y (σ y))
                 grind)
              | exact resolve b21e649271 b21e1013493
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e649271
            have b21e1017968 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op X0 (σ y))) ∨ x = X0 := by
              intro X0
              first
              | (have i₁ := b21e100 y X0
                 have i₂ := b21e1013493 X0
                 grind)
              | exact superpose b21e1013493 b21e100
              | (have j1 := b21e1013493 X0
                 grind)
              | exact resolve b21e100 b21e1013493
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e100 b21e1013493
            have b21e1018341 : x = (M.op y (σ y)) ∨ x = (M.op y (τ y)) := by
              first
              | (have r₁ := b21e1017964
                 have r₂ := b21e51
                 grind)
              | exact resolve b21e1017964 b21e51
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1017964
            have b21e1018467 : x = (σ y) ∨ x = (M.op y (τ y)) := by
              first
              | (have i₁ := b21e1018341
                 have i₂ := b21e14736
                 grind)
              | exact superpose b21e14736 b21e1018341
              | exact resolve b21e1018341 b21e14736
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1018341
            have b21e1018584 : x = (M.op y (τ y)) := by
              first
              | (have r₁ := b21e1018467
                 have r₂ := b21e2754
                 grind)
              | exact resolve b21e1018467 b21e2754
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e2754 b21e1018467
            have b21e1052308 : (τ (σ y)) = (k y (τ y)) ∨ x = y := by
              first
              | (have i₁ := b21e1017968 y
                 have i₂ := b21e14736
                 grind)
              | exact superpose b21e14736 b21e1017968
              | (have j0 := b21e1017968 y
                 grind)
              | exact resolve b21e1017968 b21e14736
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e14736 b21e1017968
            have b21e1052330 : (τ (σ y)) = (k y (τ y)) := by
              first
              | (have r₁ := b21e1052308
                 have r₂ := b21e51
                 grind)
              | exact resolve b21e1052308 b21e51
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1052308
            have b21e1052352 : y = (k y (τ y)) := by
              first
              | (have i₁ := b21e1052330
                 have i₂ := b21e15 y
                 grind)
              | exact superpose b21e15 b21e1052330
              | exact resolve b21e1052330 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1052330
            have b21e1055557 : y = (M.op (τ y) y) ∨ (τ y) = (M.op y (τ y)) := by
              first
              | (have i₁ := b21e652972 (τ y)
                 have i₂ := b21e1052352
                 grind)
              | exact superpose b21e1052352 b21e652972
              | (have j0 := b21e652972 (τ y)
                 grind)
              | exact resolve b21e652972 b21e1052352
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e652972 b21e1052352
            have b21e1055571 : y = (M.op y (τ y)) ∨ (τ y) = (M.op y (τ y)) := by
              first
              | (have i₁ := b21e1055557
                 have i₂ := b21e799 (τ y)
                 grind)
              | exact superpose b21e799 b21e1055557
              | exact resolve b21e1055557 b21e799
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e799 b21e1055557
            have b21e1055582 : x = y ∨ (τ y) = (M.op y (τ y)) := by
              first
              | (have i₁ := b21e1055571
                 have i₂ := b21e1018584
                 grind)
              | exact superpose b21e1018584 b21e1055571
              | exact resolve b21e1055571 b21e1018584
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1055571
            have b21e1055591 : (τ y) = (M.op y (τ y)) := by
              first
              | (have r₁ := b21e1055582
                 have r₂ := b21e51
                 grind)
              | exact resolve b21e1055582 b21e51
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1055582
            have b21e1055600 : x = (τ y) := by
              first
              | (have i₁ := b21e1055591
                 have i₂ := b21e1018584
                 grind)
              | exact superpose b21e1018584 b21e1055591
              | exact resolve b21e1055591 b21e1018584
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1018584 b21e1055591
            have b21e1058713 : y = (σ x) := by
              first
              | (have i₁ := b21e16 y
                 have i₂ := b21e1055600
                 grind)
              | exact superpose b21e1055600 b21e16
              | exact resolve b21e16 b21e1055600
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1055600
            have b21e1062049 : x = y := by
              first
              | (have i₁ := b21e12204
                 have i₂ := b21e1058713
                 grind)
              | exact superpose b21e1058713 b21e12204
              | exact resolve b21e12204 b21e1058713
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e12204 b21e1058713
            have b21e1062097 : False := by grind
            exact b21e1062097
          · rcases eq_or_ne (M.op y x) (x) with h2b | h2b
            · have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b22e19 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e23 : y ≠ (M.op x x) := by grind
              have b22e24 : y ≠ (M.op x y) := by grind
              have b22e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b22e26 : (σ y) = (M.op (σ x) (σ y)) := by grind
              have b22e27 : x ≠ (M.op y y) := by grind
              have b22e28 : x = (M.op y x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e45 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b22e19 (σ x) (σ y)
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e19
                | (have j0 := b22e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b22e19 (σ x) (σ y)
                   have r₂ := b22e26
                   grind)
                | exact resolve b22e19 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e47 : x ≠ x ∨ x = (M.op y y) ∨ (M.op x x) = (k y x) := by
                first
                | (have i₁ := b22e19 y x
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e19
                | (have j0 := b22e19 y x
                   grind)
                | (have r₁ := b22e19 y x
                   have r₂ := b22e28
                   grind)
                | exact resolve b22e19 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e48 : x = (M.op y y) ∨ (M.op x x) = (k y x) := by grind
              clear b22e47
              have b22e49 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
              clear b22e45
              have b22e50 : (M.op x x) = (k y x) := by
                first
                | (have r₁ := b22e48
                   have r₂ := b22e27
                   grind)
                | exact resolve b22e48 b22e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e48
              have b22e52 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
                first
                | (have r₁ := b22e49
                   have r₂ := b22e25
                   grind)
                | exact resolve b22e49 b22e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e49
              have b22e53 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b22e52
                   have i₂ := b22e21 x y
                   grind)
                | exact superpose b22e21 b22e52
                | exact resolve b22e52 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e52
              have b22e119 : (σ y) = (k (σ y) (σ (k x y))) := by grind
              clear b22e53
              have b22e123 : (σ y) = (σ (k y (k x y))) := by
                first
                | (have i₁ := b22e119
                   have i₂ := b22e21 y (k x y)
                   grind)
                | exact superpose b22e21 b22e119
                | exact resolve b22e119 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e119
              have b22e345 : (k y (k x y)) = (τ (σ y)) := by
                first
                | (have i₁ := b22e16 (k y (k x y))
                   have i₂ := b22e123
                   grind)
                | exact superpose b22e123 b22e16
                | exact resolve b22e16 b22e123
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e123
              have b22e346 : y = (k y (k x y)) := by
                first
                | (have i₁ := b22e345
                   have i₂ := b22e16 y
                   grind)
                | exact superpose b22e16 b22e345
                | exact resolve b22e345 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e345
              have b22e373 : y = (k y (M.op y x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b22e346
                   have i₂ := b22e20 x y
                   grind)
                | exact superpose b22e20 b22e346
                | (have j1 := b22e20 x y
                   grind)
                | exact resolve b22e346 b22e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e346
              have b22e379 : y = (k y (M.op y x)) ∨ y = (M.op x y) := by
                first
                | (have r₁ := b22e373
                   have r₂ := b22e23
                   grind)
                | exact resolve b22e373 b22e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e373
              have b22e381 : y = (k y (M.op y x)) := by
                first
                | (have r₁ := b22e379
                   have r₂ := b22e24
                   grind)
                | exact resolve b22e379 b22e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e379
              have b22e383 : y = (k y x) := by
                first
                | (have i₁ := b22e381
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e381
                | exact resolve b22e381 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e381
              have b22e390 : y = (M.op x x) := by
                first
                | (have i₁ := b22e50
                   have i₂ := b22e383
                   grind)
                | exact superpose b22e383 b22e50
                | exact resolve b22e50 b22e383
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e50 b22e383
              have b22e392 : False := by grind
              exact b22e392
            · have b23e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
                intro X0 X1 X2
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b23e23 : y ≠ (M.op x x) := by grind
              have b23e24 : y ≠ (M.op x y) := by grind
              have b23e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b23e26 : (σ y) = (M.op (σ x) (σ y)) := by grind
              have b23e27 : x ≠ (M.op y y) := by grind
              have b23e28 : x ≠ (M.op y x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e30 : (σ (M.op x y)) ≠ (σ y) := by
                first
                | (have i₁ := b23e22
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e22
                | exact resolve b23e22 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e33 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X0 (σ x))) := by
                intro X0
                first
                | (have i₁ := b23e15 (σ y) X0 (σ x)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e15
                | exact resolve b23e15 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X0))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e15 (M.op X1 X2) X3 (M.op X2 X0)
                   have i₂ := b23e15 X0 X1 X2
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e35 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op (σ y) X0) (σ y)) := by
                intro X0
                first
                | (have i₁ := b23e15 X0 (σ x) (σ y)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e15
                | exact resolve b23e15 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op (M.op X1 X3) X2) (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e15 X2 (M.op X3 X0) (M.op X1 X3)
                   have i₂ := b23e15 X0 X1 X3
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e44 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b23e19 (σ x) (σ y)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e19
                | (have j0 := b23e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b23e19 (σ x) (σ y)
                   have r₂ := b23e26
                   grind)
                | exact resolve b23e19 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e46 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
              clear b23e44
              have b23e47 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
                first
                | (have r₁ := b23e46
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e46 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e46
              have b23e48 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b23e47
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e47
                | exact resolve b23e47 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e47
              have b23e61 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b23e21 X1 X0
                   have i₂ := b23e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b23e20 b23e21
                | (have j1 := b23e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b23e21 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e63 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b23e73 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ y) X0) (σ (k x y))) := by
                intro X0
                first
                | (have i₁ := b23e15 X0 (σ y) (σ y)
                   have i₂ := b23e48
                   grind)
                | exact superpose b23e48 b23e15
                | exact resolve b23e15 b23e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e97 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (M.op (σ y) X0) (M.op X1 (σ y))) := by
                intro X0 X1
                first
                | (have i₁ := b23e15 (M.op X0 (σ x)) X1 (σ y)
                   have i₂ := b23e33 X0
                   grind)
                | exact superpose b23e33 b23e15
                | exact resolve b23e15 b23e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e98 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 (σ x)) X1) := by
                intro X0 X1
                first
                | (have i₁ := b23e97 X0 X1
                   have i₂ := b23e15 X0 X1 (σ y)
                   grind)
                | exact superpose b23e15 b23e97
                | exact resolve b23e97 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e97
              have b23e133 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X3 X0)) = (M.op (M.op X3 X2) (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e34 X3 X2 X1 (M.op X3 X0)
                   have i₂ := b23e15 X0 X1 X3
                   grind)
                | exact superpose b23e15 b23e34
                | exact resolve b23e34 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e167 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (M.op X0 (σ x)) (M.op X1 (σ y))) := by
                intro X0 X1
                first
                | (have i₁ := b23e36 X1 (σ y) (σ y) X0
                   have i₂ := b23e35 X0
                   grind)
                | exact superpose b23e35 b23e36
                | exact resolve b23e36 b23e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e172 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op (M.op X1 X4) X3) X2) (M.op X0 X1)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b23e36 (M.op X4 X0) (M.op X1 X4) X2 X3
                   have i₂ := b23e15 X0 X1 X4
                   grind)
                | exact superpose b23e15 b23e36
                | exact resolve b23e36 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e175 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (σ y) X0))) = (M.op (M.op (M.op (σ y) X2) X1) (M.op X0 (σ x))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e36 (M.op (σ y) X0) (σ y) X1 X2
                   have i₂ := b23e35 X0
                   grind)
                | exact superpose b23e35 b23e36
                | exact resolve b23e36 b23e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e178 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) (M.op (M.op X4 X1) X0)) = (M.op (M.op X4 X3) (M.op X0 (M.op X1 X2))) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b23e34 X4 X3 X2 (M.op (M.op X4 X1) X0)
                   have i₂ := b23e36 X2 X4 X0 X1
                   grind)
                | exact superpose b23e36 b23e34
                | exact resolve b23e34 b23e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e189 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (σ y) X0))) = (M.op (M.op X1 (σ x)) (M.op (M.op (σ y) X2) X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e175 X0 X1 X2
                   have i₂ := b23e133 X0 (σ x) X1 (M.op (σ y) X2)
                   grind)
                | (have i₁ := b23e175 x X1 X2
                   have i₂ := b23e133 (σ x) X1 (M.op (σ y) X2) x
                   grind)
                | exact superpose b23e133 b23e175
                | exact resolve b23e175 b23e133
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e175
              have b23e192 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X0))) = (M.op (M.op X2 X1) (M.op (M.op (M.op X1 X4) X3) X0)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b23e172 X0 X1 X2 X3 X4
                   have i₂ := b23e133 X0 X1 X2 (M.op (M.op X1 X4) X3)
                   grind)
                | (have i₁ := b23e172 X3 X0 X1 X3 X4
                   have i₂ := b23e133 X0 X1 (M.op (M.op X0 X4) X3) X3
                   grind)
                | exact superpose b23e133 b23e172
                | exact resolve b23e172 b23e133
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e172
              have b23e194 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op (σ y) (M.op X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b23e167 X0 X1
                   have i₂ := b23e98 X0 (M.op X1 (σ y))
                   grind)
                | exact superpose b23e98 b23e167
                | exact resolve b23e167 b23e98
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e167
              have b23e200 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (σ y) X0))) = (M.op X1 (M.op (M.op (σ y) X2) X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e189 X0 X1 X2
                   have i₂ := b23e98 X1 (M.op (M.op (σ y) X2) X0)
                   grind)
                | exact superpose b23e98 b23e189
                | exact resolve b23e189 b23e98
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e189
              have b23e235 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                first
                | (have j0 := b23e63 X1 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e63
              have b23e339 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X0)) = (M.op X1 (M.op (σ x) X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e36 X2 X0 X1 (σ x)
                   have i₂ := b23e98 X0 X1
                   grind)
                | exact superpose b23e98 b23e36
                | exact resolve b23e36 b23e98
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e340 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op X0 (M.op X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b23e15 (σ x) X1 X0
                   have i₂ := b23e98 X0 (M.op X1 X0)
                   grind)
                | exact superpose b23e98 b23e15
                | exact resolve b23e15 b23e98
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e342 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X0)) = (M.op (σ x) (M.op X1 X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e36 X2 X0 (σ x) X1
                   have i₂ := b23e98 (M.op X0 X1) (M.op X2 X0)
                   grind)
                | exact superpose b23e98 b23e36
                | exact resolve b23e36 b23e98
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e36
              have b23e348 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (σ x))) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e15 X2 (M.op X0 (σ x)) X1
                   have i₂ := b23e98 X0 X1
                   grind)
                | exact superpose b23e98 b23e15
                | exact resolve b23e15 b23e98
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e355 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X0 (σ x))) = (M.op (M.op X2 X3) (M.op X0 (M.op X1 X2))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e34 X2 X3 X1 (M.op X0 (σ x))
                   have i₂ := b23e98 X0 (M.op X1 X2)
                   grind)
                | exact superpose b23e98 b23e34
                | exact resolve b23e34 b23e98
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e98
              have b23e356 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) X0) = (M.op (M.op X3 X1) (M.op X0 (σ x))) := by
                intro X0 X1 X3
                first
                | (have i₁ := b23e355 X0 X1 x X3
                   have i₂ := b23e34 x X3 X1 X0
                   grind)
                | exact superpose b23e34 b23e355
                | exact resolve b23e355 b23e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e355
              have b23e362 : ∀ X0 X2 : G, (M.op X2 X0) = (M.op X2 (M.op X0 (σ x))) := by
                intro X0 X2
                first
                | (have i₁ := b23e348 X0 x X2
                   have i₂ := b23e15 X2 X0 x
                   grind)
                | exact superpose b23e15 b23e348
                | exact resolve b23e348 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e348
              have b23e365 : ∀ X1 X2 : G, (M.op X1 X2) = (M.op (σ x) (M.op X1 X2)) := by
                intro X1 X2
                first
                | (have i₁ := b23e342 x X1 X2
                   have i₂ := b23e15 X1 X2 x
                   grind)
                | exact superpose b23e15 b23e342
                | exact resolve b23e342 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e342
              have b23e366 : ∀ X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (σ x) X2)) := by
                intro X1 X2
                first
                | (have i₁ := b23e339 x X1 X2
                   have i₂ := b23e15 X1 X2 x
                   grind)
                | exact superpose b23e15 b23e339
                | exact resolve b23e339 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e339
              have b23e558 : (σ y) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b23e61 y y
                   have i₂ := b23e48
                   grind)
                | exact superpose b23e48 b23e61
                | exact resolve b23e61 b23e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e61
              have b23e639 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) := by grind
              clear b23e558
              have b23e710 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op X0 X1) (M.op (σ x) X0)) := by
                intro X0 X1
                first
                | (have i₁ := b23e340 (M.op X0 X1) X1
                   have i₂ := b23e340 X1 X0
                   grind)
                | exact superpose b23e340 b23e340
                | exact resolve b23e340 b23e340
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e716 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X2 X1) (M.op (σ x) X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e34 X2 X1 X0 X2
                   have i₂ := b23e340 X2 X0
                   grind)
                | exact superpose b23e340 b23e34
                | exact resolve b23e34 b23e340
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e718 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 X2) X1) (M.op (σ x) X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e15 X1 X2 (M.op X0 X2)
                   have i₂ := b23e340 X2 X0
                   grind)
                | exact superpose b23e340 b23e15
                | exact resolve b23e15 b23e340
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e721 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op (M.op X0 X2) X1) (M.op X3 (M.op (σ x) X0))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e34 (M.op X0 X2) X1 X2 X3
                   have i₂ := b23e340 X2 X0
                   grind)
                | exact superpose b23e340 b23e34
                | exact resolve b23e34 b23e340
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e735 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X1 X0) (M.op (M.op (M.op X0 X2) (σ x)) X3)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e721 X0 X1 X2 X3
                   have i₂ := b23e178 X3 (σ x) X0 X1 (M.op X0 X2)
                   grind)
                | exact superpose b23e178 b23e721
                | exact resolve b23e721 b23e178
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e178 b23e721
              have b23e736 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X0) (M.op (M.op X0 X2) (σ x))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e718 X0 X1 X2
                   have i₂ := b23e133 (σ x) X0 X1 (M.op X0 X2)
                   grind)
                | (have i₁ := b23e718 X0 X1 X2
                   have i₂ := b23e133 X0 X1 (M.op X0 X2) (σ x)
                   grind)
                | exact superpose b23e133 b23e718
                | exact resolve b23e718 b23e133
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e133 b23e718
              have b23e737 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X0) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e716 X0 X1 X2
                   have i₂ := b23e366 (M.op X2 X1) X0
                   grind)
                | (have i₁ := b23e716 X0 X1 X2
                   have i₂ := b23e366 (M.op X2 X1) (M.op (σ x) X0)
                   grind)
                | exact superpose b23e366 b23e716
                | exact resolve b23e716 b23e366
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e716
              have b23e739 : ∀ X1 : G, (M.op X1 (σ x)) = (M.op (σ x) X1) := by
                intro X1
                first
                | (have i₁ := b23e710 x X1
                   have i₂ := b23e15 X1 (σ x) x
                   grind)
                | exact superpose b23e15 b23e710
                | exact resolve b23e710 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e710
              have b23e751 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X1 (M.op (σ x) (M.op X2 X3))) := by
                intro X1 X2 X3
                first
                | (have i₁ := b23e735 x X1 X2 X3
                   have i₂ := b23e192 X3 x X1 (σ x) X2
                   grind)
                | exact superpose b23e192 b23e735
                | exact resolve b23e735 b23e192
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e192 b23e735
              have b23e752 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e736 X0 X1 X2
                   have i₂ := b23e356 (M.op X0 X2) X0 X1
                   grind)
                | (have i₁ := b23e736 X1 x X2
                   have i₂ := b23e356 (M.op (M.op X1 X2) (σ x)) X1 x
                   grind)
                | exact superpose b23e356 b23e736
                | exact resolve b23e736 b23e356
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e356 b23e736
              have b23e754 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X1 (M.op X2 X3)) := by
                intro X1 X2 X3
                first
                | (have i₁ := b23e751 X1 X2 X3
                   have i₂ := b23e366 X1 (M.op X2 X3)
                   grind)
                | (have i₁ := b23e751 X1 X2 X3
                   have i₂ := b23e366 X1 (M.op (σ x) (M.op X2 X3))
                   grind)
                | exact superpose b23e366 b23e751
                | exact resolve b23e751 b23e366
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e751
              have b23e858 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (σ x))) := by
                intro X0
                first
                | (have i₁ := b23e340 X0 (σ x)
                   have i₂ := b23e739 X0
                   grind)
                | (have i₁ := b23e340 (σ x) x
                   have i₂ := b23e739 x
                   grind)
                | exact superpose b23e739 b23e340
                | exact resolve b23e340 b23e739
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e859 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ x)) := by
                intro X0
                first
                | (have i₁ := b23e858 X0
                   have i₂ := b23e362 X0 X0
                   grind)
                | (have i₁ := b23e858 x
                   have i₂ := b23e362 (M.op x (σ x)) x
                   grind)
                | exact superpose b23e362 b23e858
                | exact resolve b23e858 b23e362
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e858
              have b23e1288 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
                intro X0 X1
                first
                | (have i₁ := b23e859 X0
                   have i₂ := b23e859 X1
                   grind)
                | (have i₁ := b23e859 X0
                   have i₂ := b23e859 (σ x)
                   grind)
                | exact superpose b23e859 b23e859
                | exact resolve b23e859 b23e859
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e1323 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) := by
                intro X0
                first
                | (have i₁ := b23e25
                   have i₂ := b23e859 X0
                   grind)
                | (have i₁ := b23e25
                   have i₂ := b23e859 (σ x)
                   grind)
                | exact superpose b23e859 b23e25
                | exact resolve b23e25 b23e859
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e859
              have b23e1526 : (σ y) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b23e1323 (σ y)
                   have i₂ := b23e48
                   grind)
                | exact superpose b23e48 b23e1323
                | exact resolve b23e1323 b23e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e48
              have b23e1752 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 X0) (σ y)) := by
                intro X0
                first
                | (have i₁ := b23e35 (σ y)
                   have i₂ := b23e1288 (σ y) X0
                   grind)
                | (have i₁ := b23e35 (σ y)
                   have i₂ := b23e1288 X0 (σ y)
                   grind)
                | exact superpose b23e1288 b23e35
                | exact resolve b23e35 b23e1288
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e35
              have b23e1754 : ∀ X0 : G, (M.op X0 X0) ≠ y := by
                intro X0
                first
                | (have i₁ := b23e23
                   have i₂ := b23e1288 x X0
                   grind)
                | (have i₁ := b23e23
                   have i₂ := b23e1288 X0 x
                   grind)
                | exact superpose b23e1288 b23e23
                | exact resolve b23e23 b23e1288
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1288
              have b23e1762 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op X0 (M.op X0 (σ y))) := by
                intro X0
                first
                | (have i₁ := b23e1752 X0
                   have i₂ := b23e754 X0 X0 (σ y)
                   grind)
                | exact superpose b23e754 b23e1752
                | exact resolve b23e1752 b23e754
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1752
              have b23e1808 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (σ y))) := by
                intro X0
                first
                | (have i₁ := b23e1762 X0
                   have i₂ := b23e739 (σ y)
                   grind)
                | exact superpose b23e739 b23e1762
                | exact resolve b23e1762 b23e739
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e739 b23e1762
              have b23e1838 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ y))) := by
                intro X0
                first
                | (have i₁ := b23e1808 X0
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e1808
                | exact resolve b23e1808 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1808
              have b23e1914 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
                intro X0
                first
                | (have i₁ := b23e340 (σ y) X0
                   have i₂ := b23e194 (σ y) X0
                   grind)
                | (have i₁ := b23e340 (σ y) X0
                   have i₂ := b23e194 X0 (σ y)
                   grind)
                | exact superpose b23e194 b23e340
                | exact resolve b23e340 b23e194
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e340
              have b23e1935 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ y) (M.op (M.op (σ y) X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b23e15 X0 X1 (σ y)
                   have i₂ := b23e194 (M.op (σ y) X0) X1
                   grind)
                | exact superpose b23e194 b23e15
                | exact resolve b23e15 b23e194
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e1941 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ x) (σ y))) := by
                intro X0
                first
                | (have i₁ := b23e33 X0
                   have i₂ := b23e194 X0 (σ x)
                   grind)
                | exact superpose b23e194 b23e33
                | exact resolve b23e33 b23e194
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e33 b23e194
              have b23e1972 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b23e1941 X0
                   have i₂ := b23e366 X0 (σ y)
                   grind)
                | (have i₁ := b23e1941 x
                   have i₂ := b23e366 x (M.op (σ x) (σ y))
                   grind)
                | exact superpose b23e366 b23e1941
                | exact resolve b23e1941 b23e366
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e366 b23e1941
              have b23e1978 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ y) (M.op X0 (M.op (σ y) X1))) := by
                intro X0 X1
                first
                | (have i₁ := b23e1935 X0 X1
                   have i₂ := b23e200 X1 (σ y) X0
                   grind)
                | (have i₁ := b23e1935 X0 (M.op (σ y) X0)
                   have i₂ := b23e200 X0 (σ y) (M.op (σ y) X0)
                   grind)
                | exact superpose b23e200 b23e1935
                | exact resolve b23e1935 b23e200
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1935
              have b23e2262 : ∀ X0 X1 : G, (M.op (σ (k x y)) X1) = (M.op (M.op X0 (σ y)) (M.op X1 (M.op (σ y) X0))) := by
                intro X0 X1
                first
                | (have i₁ := b23e15 (σ (k x y)) X1 (M.op (σ y) X0)
                   have i₂ := b23e73 X0
                   grind)
                | exact superpose b23e73 b23e15
                | exact resolve b23e15 b23e73
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e2284 : ∀ X1 : G, (M.op (σ (k x y)) X1) = (M.op (M.op (σ y) (σ y)) X1) := by
                intro X1
                first
                | (have i₁ := b23e2262 x X1
                   have i₂ := b23e34 x (σ y) (σ y) X1
                   grind)
                | exact superpose b23e34 b23e2262
                | exact resolve b23e2262 b23e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e34 b23e2262
              have b23e2311 : ∀ X1 : G, (M.op (σ (k x y)) X1) = (M.op (σ y) (M.op (σ y) X1)) := by
                intro X1
                first
                | (have i₁ := b23e2284 X1
                   have i₂ := b23e754 (σ y) (σ y) X1
                   grind)
                | exact superpose b23e754 b23e2284
                | exact resolve b23e2284 b23e754
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e2284
              have b23e2336 : ∀ X1 : G, (M.op (σ x) X1) = (M.op (σ (k x y)) X1) := by
                intro X1
                first
                | (have i₁ := b23e2311 X1
                   have i₂ := b23e1914 X1
                   grind)
                | exact superpose b23e1914 b23e2311
                | exact resolve b23e2311 b23e1914
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1914 b23e2311
              have b23e3827 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b23e235 (σ y) (σ x)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e235
                | (have j0 := b23e235 (σ y) (σ x)
                   grind)
                | (have r₁ := b23e235 (σ y) (σ x)
                   have r₂ := b23e26
                   grind)
                | exact resolve b23e235 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e235
              have b23e3851 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
              clear b23e3827
              have b23e3866 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b23e3851
                   have i₂ := b23e21 y x
                   grind)
                | exact superpose b23e21 b23e3851
                | exact resolve b23e3851 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e3851
              have b23e3875 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b23e3866
                   have i₂ := b23e1972 (σ x)
                   grind)
                | exact superpose b23e1972 b23e3866
                | exact resolve b23e3866 b23e1972
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1972 b23e3866
              have b23e3879 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b23e3875
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e3875
                | exact resolve b23e3875 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e3875
              have b23e6084 : (k y y) = (τ (σ (k x y))) ∨ (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b23e16 (k y y)
                   have i₂ := b23e639
                   grind)
                | exact superpose b23e639 b23e16
                | exact resolve b23e16 b23e639
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e639
              have b23e6119 : (k y y) = (τ (σ (k x y))) := by
                first
                | (have r₁ := b23e6084
                   have r₂ := b23e1526
                   grind)
                | exact resolve b23e6084 b23e1526
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1526 b23e6084
              have b23e6135 : (k x y) = (k y y) := by
                first
                | (have i₁ := b23e6119
                   have i₂ := b23e16 (k x y)
                   grind)
                | exact superpose b23e16 b23e6119
                | exact resolve b23e6119 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e6119
              have b23e6167 : (M.op y y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b23e20 y y
                   have i₂ := b23e6135
                   grind)
                | exact superpose b23e6135 b23e20
                | (have j0 := b23e20 y y
                   grind)
                | exact resolve b23e20 b23e6135
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e6135
              have b23e6168 : (M.op y y) = (k x y) ∨ y = (M.op y y) := by grind
              clear b23e6167
              have b23e6170 : (M.op y y) = (k x y) := by
                first
                | (have r₁ := b23e6168
                   have r₂ := b23e1754 y
                   grind)
                | exact resolve b23e6168 b23e1754
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1754 b23e6168
              have b23e6302 : (M.op y y) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e6170
                   grind)
                | exact superpose b23e6170 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e6170
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e6170
              have b23e6303 : (M.op y y) = (M.op y x) ∨ y = (M.op x y) := by
                first
                | (have r₁ := b23e6302
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e6302 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e6302
              have b23e6314 : (M.op y y) = (M.op y x) := by
                first
                | (have r₁ := b23e6303
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e6303 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e6303
              have b23e6960 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) X0) X1) (σ y)) = (M.op (M.op (σ y) (M.op X0 (M.op (σ y) X1))) (σ (k x y))) := by
                intro X0 X1
                first
                | (have i₁ := b23e73 (M.op (M.op (σ y) X0) X1)
                   have i₂ := b23e200 X1 (σ y) X0
                   grind)
                | exact superpose b23e200 b23e73
                | exact resolve b23e73 b23e200
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e73 b23e200
              have b23e6971 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) X0) X1) (σ y)) = (M.op (M.op (σ (k x y)) (σ y)) (M.op X0 (M.op (σ y) X1))) := by
                intro X0 X1
                first
                | (have i₁ := b23e6960 X0 X1
                   have i₂ := b23e737 (M.op X0 (M.op (σ y) X1)) (σ y) (σ (k x y))
                   grind)
                | (have i₁ := b23e6960 X0 X1
                   have i₂ := b23e737 (σ (k x y)) (M.op X0 (M.op (σ y) X1)) (σ y)
                   grind)
                | exact superpose b23e737 b23e6960
                | exact resolve b23e6960 b23e737
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e6960
              have b23e7081 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) X0) X1) (σ y)) = (M.op (σ (k x y)) (M.op (σ y) (M.op X0 (M.op (σ y) X1)))) := by
                intro X0 X1
                first
                | (have i₁ := b23e6971 X0 X1
                   have i₂ := b23e754 (σ (k x y)) (σ y) (M.op X0 (M.op (σ y) X1))
                   grind)
                | exact superpose b23e754 b23e6971
                | exact resolve b23e6971 b23e754
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e754 b23e6971
              have b23e7168 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) X0) X1) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op X0 (M.op (σ y) X1)))) := by
                intro X0 X1
                first
                | (have i₁ := b23e7081 X0 X1
                   have i₂ := b23e2336 (M.op (σ y) (M.op X0 (M.op (σ y) X1)))
                   grind)
                | exact superpose b23e2336 b23e7081
                | exact resolve b23e7081 b23e2336
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e2336 b23e7081
              have b23e7241 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) X0) X1) (σ y)) = (M.op (σ y) (M.op X0 (M.op (σ y) X1))) := by
                intro X0 X1
                first
                | (have i₁ := b23e7168 X0 X1
                   have i₂ := b23e365 (σ y) (M.op X0 (M.op (σ y) X1))
                   grind)
                | (have i₁ := b23e7168 X0 X1
                   have i₂ := b23e365 (σ x) (M.op (σ y) (M.op X0 (M.op (σ y) X1)))
                   grind)
                | exact superpose b23e365 b23e7168
                | exact resolve b23e7168 b23e365
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e365 b23e7168
              have b23e7304 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (σ y) X0) X1) (σ y)) := by
                intro X0 X1
                first
                | (have i₁ := b23e7241 X0 X1
                   have i₂ := b23e1978 X0 X1
                   grind)
                | exact superpose b23e1978 b23e7241
                | exact resolve b23e7241 b23e1978
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1978 b23e7241
              have b23e7338 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 (σ y)) (M.op (σ y) X0)) := by
                intro X0 X1
                first
                | (have i₁ := b23e7304 X0 X1
                   have i₂ := b23e737 (σ y) X1 (M.op (σ y) X0)
                   grind)
                | (have i₁ := b23e7304 X0 X0
                   have i₂ := b23e737 X0 (M.op (σ y) X0) (σ y)
                   grind)
                | exact superpose b23e737 b23e7304
                | exact resolve b23e7304 b23e737
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e737 b23e7304
              have b23e7361 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b23e7338 X0 X1
                   have i₂ := b23e752 (σ y) X1 X0
                   grind)
                | exact superpose b23e752 b23e7338
                | exact resolve b23e7338 b23e752
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e752 b23e7338
              have b23e12265 : (σ y) ≠ (M.op y x) := by
                first
                | (have i₁ := b23e1323 y
                   have i₂ := b23e6314
                   grind)
                | exact superpose b23e6314 b23e1323
                | exact resolve b23e1323 b23e6314
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1323 b23e6314
              have b23e12312 : (M.op x y) ≠ (σ y) := by
                first
                | (have i₁ := b23e12265
                   have i₂ := b23e7361 y x
                   grind)
                | (have i₁ := b23e12265
                   have i₂ := b23e7361 x y
                   grind)
                | exact superpose b23e7361 b23e12265
                | exact resolve b23e12265 b23e7361
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e7361 b23e12265
              have b23e306520 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b23e3879
                   have i₂ := b23e20 y x
                   grind)
                | exact superpose b23e20 b23e3879
                | (have j1 := b23e20 y x
                   grind)
                | exact resolve b23e3879 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e3879
              have b23e306554 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
                first
                | (have r₁ := b23e306520
                   have r₂ := b23e30
                   grind)
                | exact resolve b23e306520 b23e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e30 b23e306520
              have b23e306556 : (σ x) = (σ y) ∨ x = (M.op y x) := by
                first
                | (have r₁ := b23e306554
                   have r₂ := b23e27
                   grind)
                | exact resolve b23e306554 b23e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e306554
              have b23e306557 : (σ x) = (σ y) := by
                first
                | (have r₁ := b23e306556
                   have r₂ := b23e28
                   grind)
                | exact resolve b23e306556 b23e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e306556
              have b23e306866 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ x))) := by
                intro X0
                first
                | (have i₁ := b23e1838 X0
                   have i₂ := b23e306557
                   grind)
                | exact superpose b23e306557 b23e1838
                | exact resolve b23e1838 b23e306557
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e1838
              have b23e306870 : y = (τ (σ x)) := by
                first
                | (have i₁ := b23e16 y
                   have i₂ := b23e306557
                   grind)
                | exact superpose b23e306557 b23e16
                | exact resolve b23e16 b23e306557
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e306557
              have b23e306986 : x = y := by
                first
                | (have i₁ := b23e306870
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e306870
                | exact resolve b23e306870 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e306870
              have b23e306988 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
                intro X0
                first
                | (have i₁ := b23e306866 X0
                   have i₂ := b23e362 X0 X0
                   grind)
                | (have i₁ := b23e306866 x
                   have i₂ := b23e362 (M.op x (σ x)) x
                   grind)
                | exact superpose b23e362 b23e306866
                | exact resolve b23e306866 b23e362
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e362 b23e306866
              have b23e308288 : (σ x) ≠ (M.op x x) := by
                first
                | (have i₁ := b23e12312
                   have i₂ := b23e306986
                   grind)
                | exact superpose b23e306986 b23e12312
                | exact resolve b23e12312 b23e306986
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e12312 b23e306986
              have b23e308318 : False := by grind
              exact b23e308318
        · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
              intro X0 X1 X2
              grind
            have b24e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b24e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b24e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b24e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e22 : y ≠ (M.op x x) := by grind
            have b24e23 : y ≠ (M.op x y) := by grind
            have b24e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b24e25 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e28 : y = (k y x) := by grind
            have b24e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 (τ X0) X1
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e20
              | exact resolve b24e20 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e31 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op X0 y)) := by
              intro X0
              first
              | (have i₁ := b24e14 y X0 y
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X0))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 (M.op X1 X2) X3 (M.op X2 X0)
                 have i₂ := b24e14 X0 X1 X2
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op (M.op X1 X3) X2) (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 X2 (M.op X3 X0) (M.op X1 X3)
                 have i₂ := b24e14 X0 X1 X3
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e36 : x = (M.op x x) := by
              first
              | (have i₁ := b24e31 y
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e31
              | exact resolve b24e31 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e46 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op x X0) x) := by
              intro X0
              first
              | (have i₁ := b24e14 X0 x x
                 have i₂ := b24e36
                 grind)
              | exact superpose b24e36 b24e14
              | exact resolve b24e14 b24e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e47 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 x)) := by
              intro X0
              first
              | (have i₁ := b24e14 x X0 x
                 have i₂ := b24e36
                 grind)
              | exact superpose b24e36 b24e14
              | exact resolve b24e14 b24e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X1 X0
                 have i₂ := b24e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b24e19 b24e20
              | (have j1 := b24e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b24e20 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e59 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b24e24
                 have i₂ := b24e19 (σ x) X0
                 grind)
              | (have i₁ := b24e24
                 have i₂ := b24e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b24e19 b24e24
              | (have j1 := b24e19 (σ x) X0
                 grind)
              | (have r₁ := b24e24
                 have r₂ := b24e19 (σ x) (σ y)
                 grind)
              | exact resolve b24e24 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e71 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
              intro X0
              grind
            clear b24e29
            have b24e76 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
              intro X0
              first
              | (have i₁ := b24e71 X0
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e71
              | exact resolve b24e71 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e71
            have b24e80 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op (M.op x X1) (M.op X0 x)) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X1 (M.op x X0) x
                 have i₂ := b24e46 X0
                 grind)
              | exact superpose b24e46 b24e14
              | exact resolve b24e14 b24e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e46
            have b24e83 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op x X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e80 X0 X1
                 have i₂ := b24e14 X1 X0 x
                 grind)
              | exact superpose b24e14 b24e80
              | exact resolve b24e80 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e80
            have b24e119 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op X1 (M.op X0 x)) := by
              intro X0 X1
              first
              | (have i₁ := b24e83 (M.op X0 x) X1
                 have i₂ := b24e47 X0
                 grind)
              | exact superpose b24e47 b24e83
              | exact resolve b24e83 b24e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e47
            have b24e128 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X0)) = (M.op (M.op x X1) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e14 (M.op x X1) X2 X0
                 have i₂ := b24e83 X1 X0
                 grind)
              | exact superpose b24e83 b24e14
              | exact resolve b24e14 b24e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e130 : (M.op x y) = (M.op y x) := by
              first
              | (have i₁ := b24e31 x
                 have i₂ := b24e83 y x
                 grind)
              | exact superpose b24e83 b24e31
              | exact resolve b24e31 b24e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e31
            have b24e133 : ∀ X1 X2 : G, (M.op X1 X2) = (M.op (M.op x X1) X2) := by
              intro X1 X2
              first
              | (have i₁ := b24e128 x X1 X2
                 have i₂ := b24e14 X1 X2 x
                 grind)
              | exact superpose b24e14 b24e128
              | exact resolve b24e128 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e128
            have b24e137 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 x)) := by
              intro X0 X1
              first
              | (have i₁ := b24e119 X0 X1
                 have i₂ := b24e83 X0 X1
                 grind)
              | exact superpose b24e83 b24e119
              | exact resolve b24e119 b24e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e119
            have b24e151 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x (M.op X1 (M.op X0 x))) := by
              intro X0 X1
              first
              | (have i₁ := b24e32 x x X0 X1
                 have i₂ := b24e36
                 grind)
              | exact superpose b24e36 b24e32
              | exact resolve b24e32 b24e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e165 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X3 X0)) = (M.op (M.op X3 X2) (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e32 X3 X2 X1 (M.op X3 X0)
                 have i₂ := b24e14 X0 X1 X3
                 grind)
              | exact superpose b24e14 b24e32
              | exact resolve b24e32 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e32
            have b24e194 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x (M.op X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e151 X0 X1
                 have i₂ := b24e137 X0 X1
                 grind)
              | exact superpose b24e137 b24e151
              | exact resolve b24e151 b24e137
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e137 b24e151
            have b24e205 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e194 X0 X1
                 have i₂ := b24e133 X0 X1
                 grind)
              | (have i₁ := b24e194 X0 x
                 have i₂ := b24e133 (M.op x X0) x
                 grind)
              | exact superpose b24e133 b24e194
              | exact resolve b24e194 b24e133
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e194
            have b24e250 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op (M.op (M.op x X1) X3) X2) (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e34 X0 (M.op x X1) X2 X3
                 have i₂ := b24e83 X1 X0
                 grind)
              | exact superpose b24e83 b24e34
              | exact resolve b24e34 b24e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e34
            have b24e290 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X2 X1) (M.op (M.op (M.op x X1) X3) X0)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e250 X0 X1 X2 X3
                 have i₂ := b24e165 X0 X1 X2 (M.op (M.op x X1) X3)
                 grind)
              | (have i₁ := b24e250 X3 X0 X1 X3
                 have i₂ := b24e165 X0 X1 (M.op (M.op x X0) X3) X3
                 grind)
              | exact superpose b24e165 b24e250
              | exact resolve b24e250 b24e165
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e250
            have b24e312 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X2 X1) (M.op (M.op X1 X3) X0)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e290 X0 X1 X2 X3
                 have i₂ := b24e133 X1 X3
                 grind)
              | (have i₁ := b24e290 X0 X1 X2 X2
                 have i₂ := b24e133 (M.op x X1) X2
                 grind)
              | exact superpose b24e133 b24e290
              | exact resolve b24e290 b24e133
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e133 b24e290
            have b24e370 : ∀ X0 : G, (M.op X0 x) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b24e83 X0 x
                 have i₂ := b24e205 X0 x
                 grind)
              | exact superpose b24e205 b24e83
              | exact resolve b24e83 b24e205
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e83
            have b24e373 : ∀ X0 X1 X2 : G, (M.op X2 x) = (M.op (M.op (M.op X1 X0) X2) (M.op X0 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e14 X2 x (M.op X1 X0)
                 have i₂ := b24e205 X0 X1
                 grind)
              | exact superpose b24e205 b24e14
              | exact resolve b24e14 b24e205
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e384 : ∀ X0 X1 X2 : G, (M.op X2 x) = (M.op (M.op X2 X1) (M.op (M.op X1 X0) X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e373 X0 X1 X2
                 have i₂ := b24e165 X0 X1 X2 (M.op X1 X0)
                 grind)
              | (have i₁ := b24e373 x X0 X1
                 have i₂ := b24e165 X0 X1 (M.op X0 x) x
                 grind)
              | exact superpose b24e165 b24e373
              | exact resolve b24e373 b24e165
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e165 b24e373
            have b24e398 : ∀ X0 X2 : G, (M.op X2 x) = (M.op X2 (M.op X0 X0)) := by
              intro X0 X2
              first
              | (have i₁ := b24e384 X0 x X2
                 have i₂ := b24e312 X0 x X2 X0
                 grind)
              | exact superpose b24e312 b24e384
              | exact resolve b24e384 b24e312
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e312 b24e384
            have b24e409 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have j0 := b24e59 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e59
            have b24e410 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
              first
              | (have r₁ := b24e409
                 have r₂ := b24e25
                 grind)
              | exact resolve b24e409 b24e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e409
            have b24e411 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b24e410
                 have i₂ := b24e20 x y
                 grind)
              | exact superpose b24e20 b24e410
              | exact resolve b24e410 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e410
            have b24e1048 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b24e25
                 have i₂ := b24e53 x y
                 grind)
              | exact superpose b24e53 b24e25
              | (have j1 := b24e53 x y
                 grind)
              | (have r₁ := b24e25
                 have r₂ := b24e53 y x
                 grind)
              | exact resolve b24e25 b24e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e53
            have b24e1135 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b24e1048
                 have i₂ := b24e28
                 grind)
              | exact superpose b24e28 b24e1048
              | exact resolve b24e1048 b24e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e28 b24e1048
            have b24e1136 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
            clear b24e1135
            have b24e1161 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b24e1136
                 have i₂ := b24e411
                 grind)
              | exact superpose b24e411 b24e1136
              | exact resolve b24e1136 b24e411
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1136
            have b24e1786 : ∀ X0 : G, (M.op X0 X0) = (M.op x x) := by
              intro X0
              first
              | (have i₁ := b24e205 X0 X0
                 have i₂ := b24e398 X0 x
                 grind)
              | exact superpose b24e398 b24e205
              | exact resolve b24e205 b24e398
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e205 b24e398
            have b24e1799 : ∀ X0 : G, (M.op X0 X0) = x := by
              intro X0
              first
              | (have i₁ := b24e1786 X0
                 have i₂ := b24e36
                 grind)
              | exact superpose b24e36 b24e1786
              | exact resolve b24e1786 b24e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e36 b24e1786
            have b24e1943 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op (τ (σ X0)) (τ (σ X0))))) := by
              intro X0
              first
              | (have i₁ := b24e20 X0 (M.op (τ (σ X0)) (τ (σ X0)))
                 have i₂ := b24e76 (σ X0)
                 grind)
              | exact superpose b24e76 b24e20
              | exact resolve b24e20 b24e76
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e76
            have b24e1946 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) := by
              intro X0
              first
              | (have i₁ := b24e1943 X0
                 have i₂ := b24e1799 (τ (σ X0))
                 grind)
              | exact superpose b24e1799 b24e1943
              | exact resolve b24e1943 b24e1799
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1943
            have b24e2127 : (σ x) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
              first
              | (have i₁ := b24e18 (σ y) (σ x)
                 have i₂ := b24e411
                 grind)
              | exact superpose b24e411 b24e18
              | (have j0 := b24e18 (σ y) (σ x)
                 grind)
              | exact resolve b24e18 b24e411
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e2143 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
              first
              | (have r₁ := b24e2127
                 have r₂ := b24e1161
                 grind)
              | exact resolve b24e2127 b24e1161
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1161 b24e2127
            have b24e2151 : x = (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
              first
              | (have i₁ := b24e2143
                 have i₂ := b24e1799 (σ y)
                 grind)
              | exact superpose b24e1799 b24e2143
              | exact resolve b24e2143 b24e1799
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1799 b24e2143
            have b24e2154 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ x = (σ x) := by
              first
              | (have i₁ := b24e2151
                 have i₂ := b24e20 y x
                 grind)
              | exact superpose b24e20 b24e2151
              | exact resolve b24e2151 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2151
            have b24e2156 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (σ x) := by
              first
              | (have i₁ := b24e2154
                 have i₂ := b24e1946 y
                 grind)
              | exact superpose b24e1946 b24e2154
              | exact resolve b24e2154 b24e1946
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1946 b24e2154
            have b24e2157 : x = (σ x) := by
              first
              | (have r₁ := b24e2156
                 have r₂ := b24e24
                 grind)
              | exact resolve b24e2156 b24e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2156
            have b24e2158 : (σ (k x y)) = (M.op (σ y) x) := by
              first
              | (have i₁ := b24e411
                 have i₂ := b24e2157
                 grind)
              | exact superpose b24e2157 b24e411
              | exact resolve b24e411 b24e2157
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e411
            have b24e2159 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e2157
                 grind)
              | exact superpose b24e2157 b24e21
              | exact resolve b24e21 b24e2157
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2157
            have b24e2178 : (σ (M.op y x)) ≠ (M.op x (σ y)) := by
              first
              | (have i₁ := b24e2159
                 have i₂ := b24e130
                 grind)
              | exact superpose b24e130 b24e2159
              | exact resolve b24e2159 b24e130
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e130 b24e2159
            have b24e2179 : (σ (k x y)) = (M.op x (σ y)) := by
              first
              | (have i₁ := b24e2158
                 have i₂ := b24e370 (σ y)
                 grind)
              | exact superpose b24e370 b24e2158
              | exact resolve b24e2158 b24e370
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e370 b24e2158
            have b24e5114 : (σ (M.op y x)) = (M.op x (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b24e2179
                 have i₂ := b24e19 x y
                 grind)
              | exact superpose b24e19 b24e2179
              | (have j1 := b24e19 x y
                 grind)
              | exact resolve b24e2179 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2179
            have b24e5137 : y = (M.op x x) ∨ y = (M.op x y) := by
              first
              | (have r₁ := b24e5114
                 have r₂ := b24e2178
                 grind)
              | exact resolve b24e5114 b24e2178
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2178 b24e5114
            have b24e5146 : y = (M.op x y) := by
              first
              | (have r₁ := b24e5137
                 have r₂ := b24e22
                 grind)
              | exact resolve b24e5137 b24e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e5137
            have b24e5155 : False := by grind
            exact b24e5155
          · rcases eq_or_ne (M.op y x) (x) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
                intro X0 X1 X2
                grind
              have b25e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b25e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e24 : y ≠ (M.op x y) := by grind
              have b25e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b25e26 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e28 : x = (M.op y x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e32 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 y)) := by
                intro X0
                first
                | (have i₁ := b25e15 x X0 y
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X0))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 (M.op X1 X2) X3 (M.op X2 X0)
                   have i₂ := b25e15 X0 X1 X2
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e34 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x X0) x) := by
                intro X0
                first
                | (have i₁ := b25e15 X0 y x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op (M.op X1 X3) X2) (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 X2 (M.op X3 X0) (M.op X1 X3)
                   have i₂ := b25e15 X0 X1 X3
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e38 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op x X0) (M.op X1 x)) := by
                intro X0 X1
                first
                | (have i₁ := b25e15 (M.op X0 y) X1 x
                   have i₂ := b25e32 X0
                   grind)
                | exact superpose b25e32 b25e15
                | exact resolve b25e15 b25e32
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e39 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 y) X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e38 X0 X1
                   have i₂ := b25e15 X0 X1 x
                   grind)
                | exact superpose b25e15 b25e38
                | exact resolve b25e38 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e38
              have b25e53 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b25e58 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
                intro X0
                first
                | (have i₁ := b25e25
                   have i₂ := b25e20 (σ x) X0
                   grind)
                | (have i₁ := b25e25
                   have i₂ := b25e20 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b25e20 b25e25
                | (have j1 := b25e20 (σ x) X0
                   grind)
                | (have r₁ := b25e25
                   have r₂ := b25e20 (σ x) (σ y)
                   grind)
                | exact resolve b25e25 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e75 : ∀ X0 X1 : G, (M.op y X1) = (M.op X0 (M.op X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b25e15 y X1 X0
                   have i₂ := b25e39 X0 (M.op X1 X0)
                   grind)
                | exact superpose b25e39 b25e15
                | exact resolve b25e15 b25e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e76 : (M.op x x) = (M.op y y) := by
                first
                | (have i₁ := b25e34 y
                   have i₂ := b25e39 x x
                   grind)
                | exact superpose b25e39 b25e34
                | exact resolve b25e34 b25e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e80 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 y)) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 X2 (M.op X0 y) X1
                   have i₂ := b25e39 X0 X1
                   grind)
                | exact superpose b25e39 b25e15
                | exact resolve b25e15 b25e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e82 : ∀ X0 X2 : G, (M.op X2 X0) = (M.op X2 (M.op X0 y)) := by
                intro X0 X2
                first
                | (have i₁ := b25e80 X0 x X2
                   have i₂ := b25e15 X2 X0 x
                   grind)
                | exact superpose b25e15 b25e80
                | exact resolve b25e80 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e80
              have b25e102 : (M.op x y) = (M.op x (M.op x x)) := by
                first
                | (have i₁ := b25e32 y
                   have i₂ := b25e76
                   grind)
                | exact superpose b25e76 b25e32
                | exact resolve b25e32 b25e76
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e32 b25e76
              have b25e108 : (M.op x y) = (M.op y x) := by
                first
                | (have i₁ := b25e102
                   have i₂ := b25e75 x x
                   grind)
                | exact superpose b25e75 b25e102
                | exact resolve b25e102 b25e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e102
              have b25e109 : x = (M.op x y) := by
                first
                | (have i₁ := b25e108
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e108
                | exact resolve b25e108 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e108
              have b25e125 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x (M.op X1 (M.op X0 y))) := by
                intro X0 X1
                first
                | (have i₁ := b25e33 y x X0 X1
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e33
                | exact resolve b25e33 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e130 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op x X0)) X2) = (M.op (M.op x X1) (M.op X2 (M.op X0 y))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e33 x X1 (M.op x X0) X2
                   have i₂ := b25e34 X0
                   grind)
                | exact superpose b25e34 b25e33
                | exact resolve b25e33 b25e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e142 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op X2 (M.op X1 (M.op X0 X2))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e39 X2 (M.op X1 (M.op X0 X2))
                   have i₂ := b25e33 X2 y X0 X1
                   grind)
                | exact superpose b25e33 b25e39
                | exact resolve b25e39 b25e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e33
              have b25e158 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op x X0)) X2) = (M.op (M.op x X1) (M.op X2 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e130 X0 X1 X2
                   have i₂ := b25e82 X0 X2
                   grind)
                | (have i₁ := b25e130 X0 X1 X2
                   have i₂ := b25e82 (M.op X0 y) X2
                   grind)
                | exact superpose b25e82 b25e130
                | exact resolve b25e130 b25e82
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e130
              have b25e161 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x (M.op X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b25e125 X0 X1
                   have i₂ := b25e82 X0 X1
                   grind)
                | (have i₁ := b25e125 X0 x
                   have i₂ := b25e82 (M.op X0 y) x
                   grind)
                | exact superpose b25e82 b25e125
                | exact resolve b25e125 b25e82
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e125
              have b25e189 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op X0 y) (M.op X1 x)) := by
                intro X0 X1
                first
                | (have i₁ := b25e35 X1 x x X0
                   have i₂ := b25e34 X0
                   grind)
                | exact superpose b25e34 b25e35
                | exact resolve b25e35 b25e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e200 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op x X1) X0) x) := by
                intro X0 X1
                first
                | (have i₁ := b25e35 y x X0 X1
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e35
                | exact resolve b25e35 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e204 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 X2)) = (M.op y (M.op X0 X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e39 (M.op X2 X0) (M.op X1 X2)
                   have i₂ := b25e35 X1 X2 y X0
                   grind)
                | exact superpose b25e35 b25e39
                | exact resolve b25e39 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35
              have b25e219 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y (M.op X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e204 X0 X1 x
                   have i₂ := b25e15 X0 X1 x
                   grind)
                | exact superpose b25e15 b25e204
                | exact resolve b25e204 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e204
              have b25e223 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op x (M.op X0 X1)) x) := by
                intro X0 X1
                first
                | (have i₁ := b25e200 X0 X1
                   have i₂ := b25e161 X1 X0
                   grind)
                | exact superpose b25e161 b25e200
                | exact resolve b25e200 b25e161
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e161 b25e200
              have b25e231 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op X0 (M.op X1 x)) := by
                intro X0 X1
                first
                | (have i₁ := b25e189 X0 X1
                   have i₂ := b25e39 X0 (M.op X1 x)
                   grind)
                | exact superpose b25e39 b25e189
                | exact resolve b25e189 b25e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e39 b25e189
              have b25e244 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op X0 X1) y) := by
                intro X0 X1
                first
                | (have i₁ := b25e223 X0 X1
                   have i₂ := b25e34 (M.op X0 X1)
                   grind)
                | exact superpose b25e34 b25e223
                | exact resolve b25e223 b25e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e34 b25e223
              have b25e258 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) y) := by
                intro X0 X1
                first
                | (have i₁ := b25e244 X0 X1
                   have i₂ := b25e82 X1 X0
                   grind)
                | (have i₁ := b25e244 x X1
                   have i₂ := b25e82 (M.op X1 y) x
                   grind)
                | exact superpose b25e82 b25e244
                | exact resolve b25e244 b25e82
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e82 b25e244
              have b25e274 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                first
                | (have j0 := b25e53 X1 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e53
              have b25e281 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have j0 := b25e58 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e58
              have b25e282 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
                first
                | (have r₁ := b25e281
                   have r₂ := b25e26
                   grind)
                | exact resolve b25e281 b25e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e281
              have b25e283 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b25e282
                   have i₂ := b25e21 x y
                   grind)
                | exact superpose b25e21 b25e282
                | exact resolve b25e282 b25e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e282
              have b25e297 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op y X2) (M.op X0 X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 X2 (M.op X0 X1) y
                   have i₂ := b25e258 X0 X1
                   grind)
                | exact superpose b25e258 b25e15
                | exact resolve b25e15 b25e258
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e258
              have b25e385 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) (M.op X2 X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 (M.op X0 X1) X2 X1
                   have i₂ := b25e75 X1 X0
                   grind)
                | exact superpose b25e75 b25e15
                | exact resolve b25e15 b25e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e75
              have b25e407 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op X2 X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e385 X0 X1 X2
                   have i₂ := b25e297 X2 X1 X0
                   grind)
                | exact superpose b25e297 b25e385
                | exact resolve b25e385 b25e297
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e297 b25e385
              have b25e6232 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op X1 x)) = (M.op (M.op x (M.op X0 x)) X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e158 x X0 X1
                   have i₂ := b25e231 X0 x
                   grind)
                | (have i₁ := b25e158 X1 x x
                   have i₂ := b25e231 x X1
                   grind)
                | exact superpose b25e231 b25e158
                | exact resolve b25e158 b25e231
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e158 b25e231
              have b25e6435 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op X1 x)) = (M.op x (M.op X1 (M.op X0 x))) := by
                intro X0 X1
                first
                | (have i₁ := b25e6232 X0 X1
                   have i₂ := b25e407 x (M.op X0 x) X1
                   grind)
                | exact superpose b25e407 b25e6232
                | exact resolve b25e6232 b25e407
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e6232
              have b25e6543 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op X1 x)) = (M.op (M.op y X0) X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e6435 X0 X1
                   have i₂ := b25e142 X0 X1 x
                   grind)
                | exact superpose b25e142 b25e6435
                | exact resolve b25e6435 b25e142
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e142 b25e6435
              have b25e6649 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op X1 x)) = (M.op y (M.op X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b25e6543 X0 X1
                   have i₂ := b25e407 y X0 X1
                   grind)
                | exact superpose b25e407 b25e6543
                | exact resolve b25e6543 b25e407
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e407 b25e6543
              have b25e6748 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op x X0) (M.op X1 x)) := by
                intro X0 X1
                first
                | (have i₁ := b25e6649 X0 X1
                   have i₂ := b25e219 X1 X0
                   grind)
                | exact superpose b25e219 b25e6649
                | exact resolve b25e6649 b25e219
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e219 b25e6649
              have b25e6835 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b25e6748 X1 X0
                   have i₂ := b25e15 X1 X0 x
                   grind)
                | exact superpose b25e15 b25e6748
                | exact resolve b25e6748 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e6748
              have b25e7155 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b25e283
                   have i₂ := b25e6835 (σ y) (σ x)
                   grind)
                | (have i₁ := b25e283
                   have i₂ := b25e6835 (σ x) (σ y)
                   grind)
                | exact superpose b25e6835 b25e283
                | exact resolve b25e283 b25e6835
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e283 b25e6835
              have b25e11206 : x ≠ x ∨ x = (k x y) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b25e274 x y
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e274
                | (have j0 := b25e274 x y
                   grind)
                | (have r₁ := b25e274 x y
                   have r₂ := b25e28
                   grind)
                | exact resolve b25e274 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e274
              have b25e11210 : x = (k x y) ∨ y = (M.op x y) := by grind
              clear b25e11206
              have b25e11213 : x = (k x y) := by
                first
                | (have r₁ := b25e11210
                   have r₂ := b25e24
                   grind)
                | exact resolve b25e11210 b25e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e11210
              have b25e112104 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e7155
                   grind)
                | exact superpose b25e7155 b25e22
                | exact resolve b25e22 b25e7155
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e7155
              have b25e112242 : (σ (M.op x y)) ≠ (σ x) := by
                first
                | (have i₁ := b25e112104
                   have i₂ := b25e11213
                   grind)
                | exact superpose b25e11213 b25e112104
                | exact resolve b25e112104 b25e11213
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e11213 b25e112104
              have b25e112308 : (σ x) ≠ (σ x) := by
                first
                | (have i₁ := b25e112242
                   have i₂ := b25e109
                   grind)
                | exact superpose b25e109 b25e112242
                | exact resolve b25e112242 b25e109
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e109 b25e112242
              have b25e112309 : False := by grind
              exact b25e112309
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X1 X2)) := by
                intro X0 X1 X2
                grind
              have b26e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e23 : y ≠ (M.op x x) := by grind
              have b26e24 : y ≠ (M.op x y) := by grind
              have b26e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b26e26 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X0))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 (M.op X1 X2) X3 (M.op X2 X0)
                   have i₂ := b26e15 X0 X1 X2
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e61 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
                intro X0
                first
                | (have i₁ := b26e25
                   have i₂ := b26e20 (σ x) X0
                   grind)
                | (have i₁ := b26e25
                   have i₂ := b26e20 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b26e20 b26e25
                | (have j1 := b26e20 (σ x) X0
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e20 (σ x) (σ y)
                   grind)
                | exact resolve b26e25 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e98 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X3 X0)) = (M.op (M.op X3 X2) (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e32 X3 X2 X1 (M.op X3 X0)
                   have i₂ := b26e15 X0 X1 X3
                   grind)
                | exact superpose b26e15 b26e32
                | exact resolve b26e32 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e32
              have b26e211 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have j0 := b26e61 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e61
              have b26e212 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
                first
                | (have r₁ := b26e211
                   have r₂ := b26e26
                   grind)
                | exact resolve b26e211 b26e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e211
              have b26e213 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b26e212
                   have i₂ := b26e21 x y
                   grind)
                | exact superpose b26e21 b26e212
                | exact resolve b26e212 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e212
              have b26e1146 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e15 X2 X0 X1
                   have i₂ := b26e98 X1 X2 X1 X0
                   grind)
                | (have i₁ := b26e15 X2 X0 X1
                   have i₂ := b26e98 X0 X1 X2 X1
                   grind)
                | exact superpose b26e98 b26e15
                | exact resolve b26e15 b26e98
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1168 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e15 X0 X2 X1
                   have i₂ := b26e98 X2 X1 X0 X1
                   grind)
                | (have i₁ := b26e15 X1 x X0
                   have i₂ := b26e98 X0 X1 X0 x
                   grind)
                | exact superpose b26e98 b26e15
                | exact resolve b26e15 b26e98
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e98
              have b26e17168 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e1146 X1 x X0
                   have i₂ := b26e1168 X1 x X0
                   grind)
                | exact superpose b26e1168 b26e1146
                | exact resolve b26e1146 b26e1168
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1146 b26e1168
              have b26e19536 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b26e213
                   have i₂ := b26e17168 (σ y) (σ x)
                   grind)
                | (have i₁ := b26e213
                   have i₂ := b26e17168 (σ x) (σ y)
                   grind)
                | exact superpose b26e17168 b26e213
                | exact resolve b26e213 b26e17168
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e213
              have b26e21826 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e19536
                   grind)
                | exact superpose b26e19536 b26e22
                | exact resolve b26e22 b26e19536
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e19536
              have b26e26276 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b26e21826
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e21826
                | (have j1 := b26e20 x y
                   grind)
                | exact resolve b26e21826 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e21826
              have b26e26277 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op x y) := by
                first
                | (have r₁ := b26e26276
                   have r₂ := b26e23
                   grind)
                | exact resolve b26e26276 b26e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e26276
              have b26e26281 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
                first
                | (have r₁ := b26e26277
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e26277 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e26277
              have b26e26286 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
                first
                | (have i₁ := b26e26281
                   have i₂ := b26e17168 y x
                   grind)
                | (have i₁ := b26e26281
                   have i₂ := b26e17168 x y
                   grind)
                | exact superpose b26e17168 b26e26281
                | exact resolve b26e26281 b26e17168
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e17168 b26e26281
              have b26e26287 : False := by grind
              exact b26e26287
