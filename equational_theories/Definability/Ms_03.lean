import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation455`: `x = x ◇ (y ◇ (z ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_x_pxy_pyx_Equation455 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law455 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law455.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
          intro X0 X1 X2
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op y y) := by grind
        have b0e21 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e34 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
          intro X0
          first
          | (have i₁ := b0e12 X0 (σ y) (σ y)
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e12
          | exact resolve b0e12 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e36 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
          intro X0
          first
          | (have i₁ := b0e12 X0 y y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e12
          | exact resolve b0e12 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e38 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b0e12 X1 (M.op X0 X0) X0
             have i₂ := b0e12 (M.op X0 X0) X0 X0
             grind)
          | exact superpose b0e12 b0e12
          | exact resolve b0e12 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e41 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b0e36 X0
             have i₂ := b0e38 y y
             grind)
          | exact superpose b0e38 b0e36
          | exact resolve b0e36 b0e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e36
        have b0e43 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b0e34 X0
             have i₂ := b0e38 (σ y) (σ y)
             grind)
          | exact superpose b0e38 b0e34
          | exact resolve b0e34 b0e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e34 b0e38
        have b0e74 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e43 (σ x)
             grind)
          | exact superpose b0e43 b0e19
          | exact resolve b0e19 b0e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e43
        have b0e77 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b0e74
             have i₂ := b0e41 x
             grind)
          | exact superpose b0e41 b0e74
          | exact resolve b0e74 b0e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41 b0e74
        have b0e78 : False := by grind
        exact b0e78
      · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
            intro X0 X1 X2
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
          have b1e24 : x = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e20
            | exact resolve b1e20 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e36 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
            intro X0
            first
            | (have i₁ := b1e13 X0 (σ y) (σ y)
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e13
            | exact resolve b1e13 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e39 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X1 (M.op X0 X0) X0
               have i₂ := b1e13 (M.op X0 X0) X0 X0
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e43 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b1e36 X0
               have i₂ := b1e39 (σ y) (σ y)
               grind)
            | exact superpose b1e39 b1e36
            | exact resolve b1e36 b1e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e36 b1e39
          have b1e59 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b1e25
               have i₂ := b1e43 (σ x)
               grind)
            | exact superpose b1e43 b1e25
            | (have r₁ := b1e25
               have r₂ := b1e43 (σ x)
               grind)
            | exact resolve b1e25 b1e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e25 b1e43
          have b1e60 : False := by grind
          exact b1e60
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
            intro X0 X1 X2
            grind
          have b2e21 : y = (M.op y y) := by grind
          have b2e24 : x ≠ (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e33 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
            intro X0
            first
            | (have i₁ := b2e13 X0 y y
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e37 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X1 (M.op X0 X0) X0
               have i₂ := b2e13 (M.op X0 X0) X0 X0
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e42 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b2e33 X0
               have i₂ := b2e37 y y
               grind)
            | exact superpose b2e37 b2e33
            | exact resolve b2e33 b2e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e33 b2e37
          have b2e45 : x ≠ x := by
            first
            | (have i₁ := b2e24
               have i₂ := b2e42 x
               grind)
            | exact superpose b2e42 b2e24
            | (have r₁ := b2e24
               have r₂ := b2e42 x
               grind)
            | exact resolve b2e24 b2e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e42
          have b2e46 : False := by grind
          exact b2e46
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
            intro X0 X1 X2
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e21 : y = (M.op y y) := by grind
          have b3e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b3e23 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e25 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
          have b3e28 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b3e25 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e25
          have b3e34 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
            intro X0
            first
            | (have i₁ := b3e13 X0 y y
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e13
            | exact resolve b3e13 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e36 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b3e13 X1 (M.op X0 X0) X0
               have i₂ := b3e13 (M.op X0 X0) X0 X0
               grind)
            | exact superpose b3e13 b3e13
            | exact resolve b3e13 b3e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e39 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b3e34 X0
               have i₂ := b3e36 y y
               grind)
            | exact superpose b3e36 b3e34
            | exact resolve b3e34 b3e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e34 b3e36
          have b3e49 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b3e17 (σ x) (σ y)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e17
            | (have j0 := b3e17 (σ x) (σ y)
               grind)
            | (have r₁ := b3e17 (σ x) (σ y)
               have r₂ := b3e23
               grind)
            | exact resolve b3e17 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e50 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b3e49
          have b3e53 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e50
               have r₂ := b3e22
               grind)
            | exact resolve b3e50 b3e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e50
          have b3e54 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b3e53
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e53
            | exact resolve b3e53 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e53
          have b3e55 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b3e54
               have i₂ := b3e28 x
               grind)
            | exact superpose b3e28 b3e54
            | exact resolve b3e54 b3e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e28 b3e54
          have b3e99 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e55
               grind)
            | exact superpose b3e55 b3e20
            | exact resolve b3e20 b3e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e55
          have b3e104 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b3e99
               have i₂ := b3e39 x
               grind)
            | exact superpose b3e39 b3e99
            | exact resolve b3e99 b3e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e39 b3e99
          have b3e105 : False := by grind
          exact b3e105
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b4e22 : y = (M.op y y) := by grind
            have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            have b4e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e27 : (σ x) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b4e21
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e21
              | exact resolve b4e21 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e28 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
            have b4e29 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b4e28 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e28
            have b4e50 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
            have b4e53 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
            clear b4e50
            have b4e56 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b4e53
                 have r₂ := b4e23
                 grind)
              | exact resolve b4e53 b4e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e53
            have b4e57 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b4e56
                 have i₂ := b4e20 x y
                 grind)
              | exact superpose b4e20 b4e56
              | exact resolve b4e56 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e56
            have b4e58 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b4e57
                 have i₂ := b4e29 x
                 grind)
              | exact superpose b4e29 b4e57
              | exact resolve b4e57 b4e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e29 b4e57
            have b4e59 : False := by grind
            exact b4e59
          · have b5e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
              intro X0 X1 X2
              grind
            have b5e22 : y = (M.op y y) := by grind
            have b5e26 : x ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e31 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
              intro X0
              first
              | (have i₁ := b5e14 X0 y y
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e14
              | exact resolve b5e14 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e35 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b5e14 X1 (M.op X0 X0) X0
                 have i₂ := b5e14 (M.op X0 X0) X0 X0
                 grind)
              | exact superpose b5e14 b5e14
              | exact resolve b5e14 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e40 : ∀ X0 : G, (M.op X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b5e31 X0
                 have i₂ := b5e35 y y
                 grind)
              | exact superpose b5e35 b5e31
              | exact resolve b5e31 b5e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e31 b5e35
            have b5e43 : x ≠ x := by
              first
              | (have i₁ := b5e26
                 have i₂ := b5e40 x
                 grind)
              | exact superpose b5e40 b5e26
              | (have r₁ := b5e26
                 have r₂ := b5e40 x
                 grind)
              | exact resolve b5e26 b5e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e40
            have b5e44 : False := by grind
            exact b5e44
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
            intro X0 X1 X2
            grind
          have b6e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : y = (M.op y y) := by grind
          have b6e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b6e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e25 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b6e16 X0 y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e16
            | (have j0 := b6e16 X0 y
               grind)
            | (have r₁ := b6e16 X0 y
               have r₂ := b6e21
               grind)
            | exact resolve b6e16 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e28 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b6e25 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e25
          have b6e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b6e32 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 := by
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
          have b6e35 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b6e13 X1 (M.op X0 X0) X0
               have i₂ := b6e13 (M.op X0 X0) X0 X0
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e39 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b6e32 X0
               have i₂ := b6e35 x x
               grind)
            | exact superpose b6e35 b6e32
            | exact resolve b6e32 b6e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e32
          have b6e46 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b6e17 x X0
               have i₂ := b6e39 X0
               grind)
            | exact superpose b6e39 b6e17
            | (have j0 := b6e17 x X0
               grind)
            | (have r₁ := b6e17 x X0
               have r₂ := b6e39 X0
               grind)
            | exact resolve b6e17 b6e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e39
          have b6e47 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b6e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e46
          have b6e83 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e29 X0 y
               have i₂ := b6e28 (τ X0)
               grind)
            | exact superpose b6e28 b6e29
            | exact resolve b6e29 b6e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e28 b6e29
          have b6e88 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b6e83 X0
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e83
            | exact resolve b6e83 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e83
          have b6e659 : (σ y) ≠ (σ y) ∨ (k x (σ y)) = (M.op x (σ y)) := by
            first
            | (have i₁ := b6e22
               have i₂ := b6e47 (σ y)
               grind)
            | exact superpose b6e47 b6e22
            | (have j1 := b6e47 (σ y)
               grind)
            | (have r₁ := b6e22
               have r₂ := b6e47 (σ y)
               grind)
            | exact resolve b6e22 b6e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e47
          have b6e668 : (k x (σ y)) = (M.op x (σ y)) := by grind
          clear b6e659
          have b6e674 : x = (M.op x (σ y)) := by
            first
            | (have i₁ := b6e668
               have i₂ := b6e88 x
               grind)
            | exact superpose b6e88 b6e668
            | exact resolve b6e668 b6e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e88 b6e668
          have b6e680 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op x x))) = X0 := by
            intro X0
            first
            | (have i₁ := b6e13 X0 (σ y) x
               have i₂ := b6e674
               grind)
            | exact superpose b6e674 b6e13
            | exact resolve b6e13 b6e674
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e674
          have b6e691 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b6e680 X0
               have i₂ := b6e35 x (σ y)
               grind)
            | exact superpose b6e35 b6e680
            | exact resolve b6e680 b6e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e35 b6e680
          have b6e746 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b6e22
               have i₂ := b6e691 (σ y)
               grind)
            | exact superpose b6e691 b6e22
            | (have r₁ := b6e22
               have r₂ := b6e691 (σ y)
               grind)
            | exact resolve b6e22 b6e691
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e691
          have b6e748 : False := by grind
          exact b6e748
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
              intro X0 X1 X2
              grind
            have b7e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b7e22 : y = (M.op y y) := by grind
            have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b7e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e27 : (σ x) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b7e21
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e21
              | exact resolve b7e21 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e28 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b7e17 X0 y
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e17
              | (have j0 := b7e17 X0 y
                 grind)
              | (have r₁ := b7e17 X0 y
                 have r₂ := b7e22
                 grind)
              | exact resolve b7e17 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e29 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b7e28 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
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
            have b7e33 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 := by
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
            have b7e36 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b7e14 X1 (M.op X0 X0) X0
                 have i₂ := b7e14 (M.op X0 X0) X0 X0
                 grind)
              | exact superpose b7e14 b7e14
              | exact resolve b7e14 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e40 : ∀ X0 : G, (M.op X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b7e33 X0
                 have i₂ := b7e36 x y
                 grind)
              | exact superpose b7e36 b7e33
              | exact resolve b7e33 b7e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e33
            have b7e47 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k y X0) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b7e18 y X0
                 have i₂ := b7e40 X0
                 grind)
              | exact superpose b7e40 b7e18
              | (have j0 := b7e18 y X0
                 grind)
              | (have r₁ := b7e18 y X0
                 have r₂ := b7e40 X0
                 grind)
              | exact resolve b7e18 b7e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e40
            have b7e50 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k y X0) = (M.op y X0) := by
              intro X0
              first
              | (have j0 := b7e47 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e47
            have b7e82 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b7e30 X0 y
                 have i₂ := b7e29 (τ X0)
                 grind)
              | exact superpose b7e29 b7e30
              | exact resolve b7e30 b7e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e29 b7e30
            have b7e89 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b7e82 X0
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e82
              | exact resolve b7e82 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e82
            have b7e495 : (σ y) ≠ (σ y) ∨ (k y (σ y)) = (M.op y (σ y)) := by
              first
              | (have i₁ := b7e23
                 have i₂ := b7e50 (σ y)
                 grind)
              | exact superpose b7e50 b7e23
              | (have j1 := b7e50 (σ y)
                 grind)
              | (have r₁ := b7e23
                 have r₂ := b7e50 (σ y)
                 grind)
              | exact resolve b7e23 b7e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e50
            have b7e502 : (k y (σ y)) = (M.op y (σ y)) := by grind
            clear b7e495
            have b7e508 : y = (M.op y (σ y)) := by
              first
              | (have i₁ := b7e502
                 have i₂ := b7e89 y
                 grind)
              | exact superpose b7e89 b7e502
              | exact resolve b7e502 b7e89
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e89 b7e502
            have b7e519 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op y y))) = X0 := by
              intro X0
              first
              | (have i₁ := b7e14 X0 (σ y) y
                 have i₂ := b7e508
                 grind)
              | exact superpose b7e508 b7e14
              | exact resolve b7e14 b7e508
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e508
            have b7e521 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b7e519 X0
                 have i₂ := b7e36 y (σ y)
                 grind)
              | exact superpose b7e36 b7e519
              | exact resolve b7e519 b7e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e36 b7e519
            have b7e582 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b7e27
                 have i₂ := b7e521 (σ x)
                 grind)
              | exact superpose b7e521 b7e27
              | (have r₁ := b7e27
                 have r₂ := b7e521 (σ x)
                 grind)
              | exact resolve b7e27 b7e521
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e27 b7e521
            have b7e583 : False := by grind
            exact b7e583
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
              intro X0 X1 X2
              grind
            have b8e22 : y = (M.op y y) := by grind
            have b8e26 : x ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e31 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
              intro X0
              first
              | (have i₁ := b8e14 X0 y y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e34 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b8e14 X1 (M.op X0 X0) X0
                 have i₂ := b8e14 (M.op X0 X0) X0 X0
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e38 : ∀ X0 : G, (M.op X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b8e31 X0
                 have i₂ := b8e34 y y
                 grind)
              | exact superpose b8e34 b8e31
              | exact resolve b8e31 b8e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e31 b8e34
            have b8e41 : x ≠ x := by
              first
              | (have i₁ := b8e26
                 have i₂ := b8e38 x
                 grind)
              | exact superpose b8e38 b8e26
              | (have r₁ := b8e26
                 have r₂ := b8e38 x
                 grind)
              | exact resolve b8e26 b8e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e38
            have b8e42 : False := by grind
            exact b8e42
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
            intro X0 X1 X2
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b9e21 : y ≠ (M.op y y) := by grind
          have b9e23 : (σ y) = (M.op (σ y) (σ y)) := by grind
          have b9e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e26 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b9e16 X0 (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e16
            | (have j0 := b9e16 X0 (σ y)
               grind)
            | (have r₁ := b9e16 X0 (σ y)
               have r₂ := b9e23
               grind)
            | exact resolve b9e16 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e27 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b9e26 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e26
          have b9e32 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
            intro X0
            first
            | (have i₁ := b9e19 X0 y
               have i₂ := b9e27 (σ X0)
               grind)
            | exact superpose b9e27 b9e19
            | exact resolve b9e19 b9e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e27
          have b9e34 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 := by
            intro X0
            first
            | (have i₁ := b9e13 X0 x x
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e13
            | exact resolve b9e13 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e35 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
            intro X0
            first
            | (have i₁ := b9e13 X0 (σ y) (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e13
            | exact resolve b9e13 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e38 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b9e13 X1 (M.op X0 X0) X0
               have i₂ := b9e13 (M.op X0 X0) X0 X0
               grind)
            | exact superpose b9e13 b9e13
            | exact resolve b9e13 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e42 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b9e35 X0
               have i₂ := b9e38 (σ y) (σ y)
               grind)
            | exact superpose b9e38 b9e35
            | exact resolve b9e35 b9e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e35
          have b9e43 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b9e34 X0
               have i₂ := b9e38 x x
               grind)
            | exact superpose b9e38 b9e34
            | exact resolve b9e34 b9e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e34 b9e38
          have b9e50 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b9e17 x X0
               have i₂ := b9e43 X0
               grind)
            | exact superpose b9e43 b9e17
            | (have j0 := b9e17 x X0
               grind)
            | (have r₁ := b9e17 x X0
               have r₂ := b9e43 X0
               grind)
            | exact resolve b9e17 b9e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e43
          have b9e53 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b9e50 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e50
          have b9e58 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b9e20
               have i₂ := b9e42 (σ x)
               grind)
            | exact superpose b9e42 b9e20
            | exact resolve b9e20 b9e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e42
          have b9e616 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b9e32 x
               have i₂ := b9e53 y
               grind)
            | exact superpose b9e53 b9e32
            | (have j1 := b9e53 y
               grind)
            | exact resolve b9e32 b9e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e32 b9e53
          have b9e623 : y = (M.op y y) := by
            first
            | (have r₁ := b9e616
               have r₂ := b9e58
               grind)
            | exact resolve b9e616 b9e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e58 b9e616
          have b9e632 : False := by grind
          exact b9e632
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b10e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
              intro X0 X1 X2
              grind
            have b10e23 : y = (M.op y x) := by grind
            have b10e25 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e37 : ∀ X0 : G, (M.op X0 (M.op x (M.op y y))) = X0 := by
              intro X0
              first
              | (have i₁ := b10e14 X0 x y
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e14
              | exact resolve b10e14 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e39 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b10e14 X1 (M.op X0 X0) X0
                 have i₂ := b10e14 (M.op X0 X0) X0 X0
                 grind)
              | exact superpose b10e14 b10e14
              | exact resolve b10e14 b10e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e42 : ∀ X0 : G, (M.op X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b10e37 X0
                 have i₂ := b10e39 y x
                 grind)
              | exact superpose b10e39 b10e37
              | exact resolve b10e37 b10e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e37 b10e39
            have b10e48 : x ≠ x := by
              first
              | (have i₁ := b10e25
                 have i₂ := b10e42 x
                 grind)
              | exact superpose b10e42 b10e25
              | (have r₁ := b10e25
                 have r₂ := b10e42 x
                 grind)
              | exact resolve b10e25 b10e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e42
            have b10e49 : False := by grind
            exact b10e49
          · have b11e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
              intro X0 X1 X2
              grind
            have b11e23 : y = (M.op y x) := by grind
            have b11e25 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e39 : ∀ X0 : G, (M.op X0 (M.op x (M.op y y))) = X0 := by
              intro X0
              first
              | (have i₁ := b11e14 X0 x y
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e14
              | exact resolve b11e14 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e43 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b11e14 X1 (M.op X0 X0) X0
                 have i₂ := b11e14 (M.op X0 X0) X0 X0
                 grind)
              | exact superpose b11e14 b11e14
              | exact resolve b11e14 b11e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e48 : ∀ X0 : G, (M.op X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b11e39 X0
                 have i₂ := b11e43 y x
                 grind)
              | exact superpose b11e43 b11e39
              | exact resolve b11e39 b11e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e39 b11e43
            have b11e51 : x ≠ x := by
              first
              | (have i₁ := b11e25
                 have i₂ := b11e48 x
                 grind)
              | exact superpose b11e48 b11e25
              | (have r₁ := b11e25
                 have r₂ := b11e48 x
                 grind)
              | exact resolve b11e25 b11e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e48
            have b11e52 : False := by grind
            exact b11e52
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
              intro X0 X1 X2
              grind
            have b12e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b12e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e22 : y ≠ (M.op y y) := by grind
            have b12e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b12e25 : (σ y) = (M.op (σ y) (σ x)) := by grind
            have b12e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e32 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 := by
              intro X0
              first
              | (have i₁ := b12e14 X0 x x
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e14
              | exact resolve b12e14 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e36 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b12e14 X1 (M.op X0 X0) X0
                 have i₂ := b12e14 (M.op X0 X0) X0 X0
                 grind)
              | exact superpose b12e14 b12e14
              | exact resolve b12e14 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e41 : ∀ X0 : G, (M.op X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b12e32 X0
                 have i₂ := b12e36 x x
                 grind)
              | exact superpose b12e36 b12e32
              | exact resolve b12e32 b12e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e32 b12e36
            have b12e48 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b12e18 x X0
                 have i₂ := b12e41 X0
                 grind)
              | exact superpose b12e41 b12e18
              | (have j0 := b12e18 x X0
                 grind)
              | (have r₁ := b12e18 x X0
                 have r₂ := b12e41 X0
                 grind)
              | exact resolve b12e18 b12e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e41
            have b12e49 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b12e18 (σ x) (σ y)
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e18
              | (have j0 := b12e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b12e18 (σ x) (σ y)
                 have r₂ := b12e25
                 grind)
              | exact resolve b12e18 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e52 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
            clear b12e49
            have b12e53 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
              intro X0
              first
              | (have j0 := b12e48 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e48
            have b12e55 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b12e52
                 have r₂ := b12e24
                 grind)
              | exact resolve b12e52 b12e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e52
            have b12e56 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b12e55
                 have i₂ := b12e20 x y
                 grind)
              | exact superpose b12e20 b12e55
              | exact resolve b12e55 b12e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e55
            have b12e136 : (σ (M.op x y)) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e56
                 grind)
              | exact superpose b12e56 b12e21
              | exact resolve b12e21 b12e56
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e56
            have b12e642 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b12e136
                 have i₂ := b12e53 y
                 grind)
              | exact superpose b12e53 b12e136
              | (have j1 := b12e53 y
                 grind)
              | exact resolve b12e136 b12e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e53 b12e136
            have b12e650 : y = (M.op y y) := by grind
            clear b12e642
            have b12e657 : False := by grind
            exact b12e657
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
                intro X0 X1 X2
                grind
              have b13e24 : y = (M.op y x) := by grind
              have b13e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e35 : ∀ X0 : G, (M.op X0 (M.op x (M.op y y))) = X0 := by
                intro X0
                first
                | (have i₁ := b13e15 X0 x y
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e15
                | exact resolve b13e15 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e37 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b13e15 X1 (M.op X0 X0) X0
                   have i₂ := b13e15 (M.op X0 X0) X0 X0
                   grind)
                | exact superpose b13e15 b13e15
                | exact resolve b13e15 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e40 : ∀ X0 : G, (M.op X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b13e35 X0
                   have i₂ := b13e37 y x
                   grind)
                | exact superpose b13e37 b13e35
                | exact resolve b13e35 b13e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e35 b13e37
              have b13e46 : x ≠ x := by
                first
                | (have i₁ := b13e27
                   have i₂ := b13e40 x
                   grind)
                | exact superpose b13e40 b13e27
                | (have r₁ := b13e27
                   have r₂ := b13e40 x
                   grind)
                | exact resolve b13e27 b13e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e40
              have b13e47 : False := by grind
              exact b13e47
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
                intro X0 X1 X2
                grind
              have b14e24 : y = (M.op y x) := by grind
              have b14e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e31 : ∀ X0 : G, (M.op X0 (M.op x (M.op y y))) = X0 := by
                intro X0
                first
                | (have i₁ := b14e15 X0 x y
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e35 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X1 (M.op X0 X0) X0
                   have i₂ := b14e15 (M.op X0 X0) X0 X0
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e40 : ∀ X0 : G, (M.op X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b14e31 X0
                   have i₂ := b14e35 y x
                   grind)
                | exact superpose b14e35 b14e31
                | exact resolve b14e31 b14e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e31 b14e35
              have b14e43 : x ≠ x := by
                first
                | (have i₁ := b14e27
                   have i₂ := b14e40 x
                   grind)
                | exact superpose b14e40 b14e27
                | (have r₁ := b14e27
                   have r₂ := b14e40 x
                   grind)
                | exact resolve b14e27 b14e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e40
              have b14e44 : False := by grind
              exact b14e44
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
              intro X0 X1 X2
              grind
            have b15e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b15e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e27 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b15e17 X0 x
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e17
              | (have j0 := b15e17 X0 x
                 grind)
              | (have r₁ := b15e17 X0 x
                 have r₂ := b15e26
                 grind)
              | exact resolve b15e17 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e28 : ∀ X0 : G, (k X0 x) = X0 := by
              intro X0
              first
              | (have j0 := b15e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e27
            have b15e35 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X1 (M.op X0 X0) X0
                 have i₂ := b15e14 (M.op X0 X0) X0 X0
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e65 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e20 X1 X0
                 have i₂ := b15e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b15e19 b15e20
              | (have j1 := b15e19 (σ X0) (σ X0)
                 grind)
              | exact resolve b15e20 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e353 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b15e65 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e65
            have b15e355 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b15e353 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e353
            have b15e974 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b15e355 x
                 have i₂ := b15e28 x
                 grind)
              | exact superpose b15e28 b15e355
              | (have j0 := b15e355 x
                 grind)
              | exact resolve b15e355 b15e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e28 b15e355
            have b15e981 : (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b15e974
            have b15e1015 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
              intro X0
              first
              | (have i₁ := b15e35 (σ x) X0
                 have i₂ := b15e981
                 grind)
              | exact superpose b15e981 b15e35
              | exact resolve b15e35 b15e981
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e35 b15e981
            have b15e1134 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b15e25
                 have i₂ := b15e1015 (σ y)
                 grind)
              | exact superpose b15e1015 b15e25
              | (have r₁ := b15e25
                 have r₂ := b15e1015 (σ y)
                 grind)
              | exact resolve b15e25 b15e1015
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1015
            have b15e1135 : False := by grind
            exact b15e1135
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
                intro X0 X1 X2
                grind
              have b16e23 : y ≠ (M.op y y) := by grind
              have b16e28 : x = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e33 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 := by
                intro X0
                first
                | (have i₁ := b16e15 X0 y x
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e15
                | exact resolve b16e15 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e36 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b16e15 X1 (M.op X0 X0) X0
                   have i₂ := b16e15 (M.op X0 X0) X0 X0
                   grind)
                | exact superpose b16e15 b16e15
                | exact resolve b16e15 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e40 : ∀ X0 : G, (M.op X0 y) = X0 := by
                intro X0
                first
                | (have i₁ := b16e33 X0
                   have i₂ := b16e36 x y
                   grind)
                | exact superpose b16e36 b16e33
                | exact resolve b16e33 b16e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e33 b16e36
              have b16e44 : y ≠ y := by
                first
                | (have i₁ := b16e23
                   have i₂ := b16e40 y
                   grind)
                | exact superpose b16e40 b16e23
                | (have r₁ := b16e23
                   have r₂ := b16e40 y
                   grind)
                | exact resolve b16e23 b16e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e40
              have b16e45 : False := by grind
              exact b16e45
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
                intro X0 X1 X2
                grind
              have b17e24 : y = (M.op y x) := by grind
              have b17e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e31 : ∀ X0 : G, (M.op X0 (M.op x (M.op y y))) = X0 := by
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
              have b17e34 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b17e15 X1 (M.op X0 X0) X0
                   have i₂ := b17e15 (M.op X0 X0) X0 X0
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e38 : ∀ X0 : G, (M.op X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b17e31 X0
                   have i₂ := b17e34 y x
                   grind)
                | exact superpose b17e34 b17e31
                | exact resolve b17e31 b17e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e31 b17e34
              have b17e41 : x ≠ x := by
                first
                | (have i₁ := b17e27
                   have i₂ := b17e38 x
                   grind)
                | exact superpose b17e38 b17e27
                | (have r₁ := b17e27
                   have r₂ := b17e38 x
                   grind)
                | exact resolve b17e27 b17e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e38
              have b17e42 : False := by grind
              exact b17e42
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
            intro X0 X1 X2
            grind
          have b18e22 : y ≠ (M.op y x) := by grind
          have b18e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e33 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 := by
            intro X0
            first
            | (have i₁ := b18e13 X0 x x
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e13
            | exact resolve b18e13 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e37 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b18e13 X1 (M.op X0 X0) X0
               have i₂ := b18e13 (M.op X0 X0) X0 X0
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e42 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b18e33 X0
               have i₂ := b18e37 x x
               grind)
            | exact superpose b18e37 b18e33
            | exact resolve b18e33 b18e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e33 b18e37
          have b18e45 : y ≠ y := by
            first
            | (have i₁ := b18e22
               have i₂ := b18e42 y
               grind)
            | exact superpose b18e42 b18e22
            | (have r₁ := b18e22
               have r₂ := b18e42 y
               grind)
            | exact resolve b18e22 b18e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e42
          have b18e46 : False := by grind
          exact b18e46
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
              intro X0 X1 X2
              grind
            have b19e22 : y ≠ (M.op y y) := by grind
            have b19e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e34 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 := by
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
            have b19e38 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b19e14 X1 (M.op X0 X0) X0
                 have i₂ := b19e14 (M.op X0 X0) X0 X0
                 grind)
              | exact superpose b19e14 b19e14
              | exact resolve b19e14 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e43 : ∀ X0 : G, (M.op X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b19e34 X0
                 have i₂ := b19e38 x y
                 grind)
              | exact superpose b19e38 b19e34
              | exact resolve b19e34 b19e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e34 b19e38
            have b19e46 : y ≠ y := by
              first
              | (have i₁ := b19e22
                 have i₂ := b19e43 y
                 grind)
              | exact superpose b19e43 b19e22
              | (have r₁ := b19e22
                 have r₂ := b19e43 y
                 grind)
              | exact resolve b19e22 b19e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e43
            have b19e47 : False := by grind
            exact b19e47
          · have b20e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
              intro X0 X1 X2
              grind
            have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op y y) := by grind
            have b20e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e27 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b20e17 X0 (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e17
              | (have j0 := b20e17 X0 (σ y)
                 grind)
              | (have r₁ := b20e17 X0 (σ y)
                 have r₂ := b20e24
                 grind)
              | exact resolve b20e17 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e28 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b20e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e27
            have b20e32 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
              intro X0
              first
              | (have i₁ := b20e28 (σ X0)
                 have i₂ := b20e20 X0 y
                 grind)
              | exact superpose b20e20 b20e28
              | exact resolve b20e28 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e28
            have b20e35 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
              intro X0
              first
              | (have i₁ := b20e15 (k X0 y)
                 have i₂ := b20e32 X0
                 grind)
              | exact superpose b20e32 b20e15
              | exact resolve b20e15 b20e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e32
            have b20e36 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b20e35 X0
                 have i₂ := b20e15 X0
                 grind)
              | exact superpose b20e15 b20e35
              | exact resolve b20e35 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e35
            have b20e39 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
              intro X0
              first
              | (have i₁ := b20e14 X0 (σ y) (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e14
              | exact resolve b20e14 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e42 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b20e14 X1 (M.op X0 X0) X0
                 have i₂ := b20e14 (M.op X0 X0) X0 X0
                 grind)
              | exact superpose b20e14 b20e14
              | exact resolve b20e14 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e46 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b20e39 X0
                 have i₂ := b20e42 (σ y) (σ y)
                 grind)
              | exact superpose b20e42 b20e39
              | exact resolve b20e39 b20e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e39
            have b20e53 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b20e18 (σ y) X0
                 have i₂ := b20e46 X0
                 grind)
              | exact superpose b20e46 b20e18
              | (have j0 := b20e18 (σ y) X0
                 grind)
              | (have r₁ := b20e18 (σ y) X0
                 have r₂ := b20e46 X0
                 grind)
              | exact resolve b20e18 b20e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e46
            have b20e54 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have j0 := b20e53 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e53
            have b20e584 : (σ y) = (M.op (σ y) y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b20e36 (σ y)
                 have i₂ := b20e54 y
                 grind)
              | exact superpose b20e54 b20e36
              | (have j1 := b20e54 y
                 grind)
              | exact resolve b20e36 b20e54
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e36 b20e54
            have b20e593 : (σ y) = (M.op (σ y) y) := by
              first
              | (have r₁ := b20e584
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e584 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e584
            have b20e607 : ∀ X0 : G, (M.op X0 (M.op y (M.op (σ y) (σ y)))) = X0 := by
              intro X0
              first
              | (have i₁ := b20e14 X0 y (σ y)
                 have i₂ := b20e593
                 grind)
              | exact superpose b20e593 b20e14
              | exact resolve b20e14 b20e593
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e593
            have b20e609 : ∀ X0 : G, (M.op X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b20e607 X0
                 have i₂ := b20e42 (σ y) y
                 grind)
              | exact superpose b20e42 b20e607
              | exact resolve b20e607 b20e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e42 b20e607
            have b20e672 : y ≠ y := by
              first
              | (have i₁ := b20e22
                 have i₂ := b20e609 y
                 grind)
              | exact superpose b20e609 b20e22
              | (have r₁ := b20e22
                 have r₂ := b20e609 y
                 grind)
              | exact resolve b20e22 b20e609
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e609
            have b20e673 : False := by grind
            exact b20e673
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
              intro X0 X1 X2
              grind
            have b21e23 : y ≠ (M.op y x) := by grind
            have b21e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e31 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 := by
              intro X0
              first
              | (have i₁ := b21e14 X0 x x
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e14
              | exact resolve b21e14 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e35 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b21e14 X1 (M.op X0 X0) X0
                 have i₂ := b21e14 (M.op X0 X0) X0 X0
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e40 : ∀ X0 : G, (M.op X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b21e31 X0
                 have i₂ := b21e35 x x
                 grind)
              | exact superpose b21e35 b21e31
              | exact resolve b21e31 b21e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e31 b21e35
            have b21e43 : y ≠ y := by
              first
              | (have i₁ := b21e23
                 have i₂ := b21e40 y
                 grind)
              | exact superpose b21e40 b21e23
              | (have r₁ := b21e23
                 have r₂ := b21e40 y
                 grind)
              | exact resolve b21e23 b21e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e40
            have b21e44 : False := by grind
            exact b21e44
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b22e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
                intro X0 X1 X2
                grind
              have b22e23 : y ≠ (M.op y y) := by grind
              have b22e28 : x = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e32 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 := by
                intro X0
                first
                | (have i₁ := b22e15 X0 y x
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e15
                | exact resolve b22e15 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e36 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b22e15 X1 (M.op X0 X0) X0
                   have i₂ := b22e15 (M.op X0 X0) X0 X0
                   grind)
                | exact superpose b22e15 b22e15
                | exact resolve b22e15 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e41 : ∀ X0 : G, (M.op X0 y) = X0 := by
                intro X0
                first
                | (have i₁ := b22e32 X0
                   have i₂ := b22e36 x y
                   grind)
                | exact superpose b22e36 b22e32
                | exact resolve b22e32 b22e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e32 b22e36
              have b22e44 : y ≠ y := by
                first
                | (have i₁ := b22e23
                   have i₂ := b22e41 y
                   grind)
                | exact superpose b22e41 b22e23
                | (have r₁ := b22e23
                   have r₂ := b22e41 y
                   grind)
                | exact resolve b22e23 b22e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e41
              have b22e45 : False := by grind
              exact b22e45
            · have b23e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
                intro X0 X1 X2
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e24 : y ≠ (M.op y x) := by grind
              have b23e26 : (σ y) = (M.op (σ y) (σ x)) := by grind
              have b23e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e31 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ y)))) = X0 := by
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
              have b23e34 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b23e15 X1 (M.op X0 X0) X0
                   have i₂ := b23e15 (M.op X0 X0) X0 X0
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e38 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
                intro X0
                first
                | (have i₁ := b23e31 X0
                   have i₂ := b23e34 (σ y) (σ x)
                   grind)
                | exact superpose b23e34 b23e31
                | exact resolve b23e31 b23e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e31
              have b23e39 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
                intro X0
                first
                | (have i₁ := b23e18 X0 (σ x)
                   have i₂ := b23e38 (σ x)
                   grind)
                | exact superpose b23e38 b23e18
                | (have j0 := b23e18 X0 (σ x)
                   grind)
                | (have r₁ := b23e18 X0 (σ x)
                   have r₂ := b23e38 (σ x)
                   grind)
                | exact resolve b23e18 b23e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e41 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
                intro X0
                first
                | (have j0 := b23e39 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e39
              have b23e45 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
                intro X0
                first
                | (have i₁ := b23e19 (σ x) X0
                   have i₂ := b23e38 X0
                   grind)
                | exact superpose b23e38 b23e19
                | (have j0 := b23e19 (σ x) X0
                   grind)
                | (have r₁ := b23e19 (σ x) X0
                   have r₂ := b23e38 X0
                   grind)
                | exact resolve b23e19 b23e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e38
              have b23e46 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
                intro X0
                first
                | (have j0 := b23e45 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e45
              have b23e50 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) := by
                intro X0
                first
                | (have i₁ := b23e21 X0 x
                   have i₂ := b23e41 (σ X0)
                   grind)
                | exact superpose b23e41 b23e21
                | exact resolve b23e21 b23e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e41
              have b23e101 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
                intro X0
                first
                | (have i₁ := b23e16 (k X0 x)
                   have i₂ := b23e50 X0
                   grind)
                | exact superpose b23e50 b23e16
                | exact resolve b23e16 b23e50
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e50
              have b23e102 : ∀ X0 : G, (k X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b23e101 X0
                   have i₂ := b23e16 X0
                   grind)
                | exact superpose b23e16 b23e101
                | exact resolve b23e101 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e101
              have b23e731 : (σ x) = (M.op (σ x) x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b23e102 (σ x)
                   have i₂ := b23e46 x
                   grind)
                | exact superpose b23e46 b23e102
                | (have j1 := b23e46 x
                   grind)
                | exact resolve b23e102 b23e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e46 b23e102
              have b23e740 : (σ x) = (M.op (σ x) x) := by
                first
                | (have r₁ := b23e731
                   have r₂ := b23e27
                   grind)
                | exact resolve b23e731 b23e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e731
              have b23e750 : ∀ X0 : G, (M.op X0 (M.op x (M.op (σ x) (σ x)))) = X0 := by
                intro X0
                first
                | (have i₁ := b23e15 X0 x (σ x)
                   have i₂ := b23e740
                   grind)
                | exact superpose b23e740 b23e15
                | exact resolve b23e15 b23e740
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e740
              have b23e763 : ∀ X0 : G, (M.op X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b23e750 X0
                   have i₂ := b23e34 (σ x) x
                   grind)
                | exact superpose b23e34 b23e750
                | exact resolve b23e750 b23e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e34 b23e750
              have b23e828 : y ≠ y := by
                first
                | (have i₁ := b23e24
                   have i₂ := b23e763 y
                   grind)
                | exact superpose b23e763 b23e24
                | (have r₁ := b23e24
                   have r₂ := b23e763 y
                   grind)
                | exact resolve b23e24 b23e763
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e763
              have b23e829 : False := by grind
              exact b23e829
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
              intro X0 X1 X2
              grind
            have b24e23 : y ≠ (M.op y x) := by grind
            have b24e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e31 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 := by
              intro X0
              first
              | (have i₁ := b24e14 X0 x x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e34 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X1 (M.op X0 X0) X0
                 have i₂ := b24e14 (M.op X0 X0) X0 X0
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e38 : ∀ X0 : G, (M.op X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b24e31 X0
                 have i₂ := b24e34 x x
                 grind)
              | exact superpose b24e34 b24e31
              | exact resolve b24e31 b24e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e31 b24e34
            have b24e41 : y ≠ y := by
              first
              | (have i₁ := b24e23
                 have i₂ := b24e38 y
                 grind)
              | exact superpose b24e38 b24e23
              | (have r₁ := b24e23
                 have r₂ := b24e38 y
                 grind)
              | exact resolve b24e23 b24e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e38
            have b24e42 : False := by grind
            exact b24e42
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
                intro X0 X1 X2
                grind
              have b25e23 : y ≠ (M.op y y) := by grind
              have b25e28 : x = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e32 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 := by
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
              have b25e35 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X1 (M.op X0 X0) X0
                   have i₂ := b25e15 (M.op X0 X0) X0 X0
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e39 : ∀ X0 : G, (M.op X0 y) = X0 := by
                intro X0
                first
                | (have i₁ := b25e32 X0
                   have i₂ := b25e35 x y
                   grind)
                | exact superpose b25e35 b25e32
                | exact resolve b25e32 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e32 b25e35
              have b25e42 : y ≠ y := by
                first
                | (have i₁ := b25e23
                   have i₂ := b25e39 y
                   grind)
                | exact superpose b25e39 b25e23
                | (have r₁ := b25e23
                   have r₂ := b25e39 y
                   grind)
                | exact resolve b25e23 b25e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e39
              have b25e43 : False := by grind
              exact b25e43
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
                intro X0 X1 X2
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e23 : y ≠ (M.op y y) := by grind
              have b26e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b26e27 : x ≠ (M.op x x) := by grind
              have b26e28 : x ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 (τ X0) X1
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e21
                | exact resolve b26e21 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 (τ X0)
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e21
                | exact resolve b26e21 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e15 X1 (M.op X0 X0) X0
                   have i₂ := b26e15 (M.op X0 X0) X0 X0
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e34 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) ≠ (M.op X0 (M.op X1 (M.op X1 X0))) ∨ (k X2 (M.op X0 (M.op X1 (M.op X1 X0)))) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e18 X2 (M.op X0 (M.op X1 (M.op X1 X0)))
                   have i₂ := b26e15 (M.op X0 (M.op X1 (M.op X1 X0))) X0 X1
                   grind)
                | exact superpose b26e15 b26e18
                | (have j0 := b26e18 X2 (M.op X0 (M.op X1 (M.op X1 X0)))
                   grind)
                | (have r₁ := b26e18 X0 (M.op X1 (M.op X2 (M.op X2 X1)))
                   have r₂ := b26e15 (M.op X1 (M.op X2 (M.op X2 X1))) X1 X2
                   grind)
                | exact resolve b26e18 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e35 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X1 X0)))) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b26e34 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e34
              have b26e40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e18 X1 (M.op X0 X0)
                   have i₂ := b26e33 X0 (M.op X0 X0)
                   grind)
                | exact superpose b26e33 b26e18
                | (have j0 := b26e18 X1 (M.op X0 X0)
                   grind)
                | (have r₁ := b26e18 X0 (M.op X0 X0)
                   have r₂ := b26e33 X0 (M.op X0 X0)
                   grind)
                | exact resolve b26e18 b26e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e42 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have j0 := b26e40 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e40
              have b26e44 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X1 (M.op X2 (M.op X2 X1))) X0) = (M.op (M.op X1 (M.op X2 (M.op X2 X1))) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e19 (M.op X1 (M.op X2 (M.op X2 X1))) X0
                   have i₂ := b26e15 X0 X1 X2
                   grind)
                | exact superpose b26e15 b26e19
                | (have j0 := b26e19 (M.op X1 (M.op X2 (M.op X2 X1))) X0
                   grind)
                | (have r₁ := b26e19 (M.op X1 (M.op X2 (M.op X2 X1))) X0
                   have r₂ := b26e15 X0 X1 X2
                   grind)
                | exact resolve b26e19 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e47 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (k (M.op X1 (M.op X2 (M.op X2 X1))) X0) = (M.op (M.op X1 (M.op X2 (M.op X2 X1))) X0) := by
                intro X0 X1 X2
                first
                | (have j0 := b26e44 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e44
              have b26e52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 X0
                   have i₂ := b26e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b26e20 b26e21
                | (have j1 := b26e20 (σ X0) (σ X0)
                   grind)
                | exact resolve b26e21 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e56 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X2) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e18 X1 X0
                   have i₂ := b26e20 X2 X0
                   grind)
                | exact superpose b26e20 b26e18
                | (have j0 := b26e18 X1 X0
                   have j1 := b26e20 X2 X0
                   grind)
                | (have r₁ := b26e18 X0 X1
                   have r₂ := b26e20 X0 X1
                   grind)
                | (have r₁ := b26e18 X0 X0
                   have r₂ := b26e20 X0 X0
                   grind)
                | exact resolve b26e18 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e58 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b26e25
                   have i₂ := b26e20 X0 (σ y)
                   grind)
                | exact superpose b26e20 b26e25
                | (have j1 := b26e20 X0 (σ y)
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e20 X0 (σ y)
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e20 (σ y) (σ y)
                   grind)
                | exact resolve b26e25 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e59 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ y) X0) := by
                intro X0
                first
                | (have j0 := b26e58 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e58
              have b26e60 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = X0 := by
                intro X0 X1 X2
                first
                | (have j0 := b26e56 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e56
              have b26e64 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e29 X1 X0
                   have i₂ := b26e20 (τ X1) X0
                   grind)
                | exact superpose b26e20 b26e29
                | (have j1 := b26e20 X0 X0
                   grind)
                | exact resolve b26e29 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e67 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (k (τ X0) X1)
                   have i₂ := b26e29 X0 X1
                   grind)
                | exact superpose b26e29 b26e16
                | exact resolve b26e16 b26e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e29
              have b26e75 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (k X0 (τ X1))
                   have i₂ := b26e30 X1 X0
                   grind)
                | exact superpose b26e30 b26e16
                | exact resolve b26e16 b26e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e139 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e67 X1 (τ X0)
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e67
                | exact resolve b26e67 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e67
              have b26e151 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b26e21 X0 y
                   have i₂ := b26e59 (σ X0)
                   grind)
                | exact superpose b26e59 b26e21
                | (have j1 := b26e59 (σ X0)
                   grind)
                | exact resolve b26e21 b26e59
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e59
              have b26e158 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e75 X0 (M.op X1 X1)
                   have i₂ := b26e42 X1 (σ X0)
                   grind)
                | exact superpose b26e42 b26e75
                | exact resolve b26e75 b26e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e42
              have b26e159 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (M.op X2 X1))))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e75 X0 (M.op X1 (M.op X2 (M.op X2 X1)))
                   have i₂ := b26e35 X1 X2 (σ X0)
                   grind)
                | exact superpose b26e35 b26e75
                | exact resolve b26e75 b26e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e35 b26e75
              have b26e174 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (M.op X2 X1))))) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e159 X0 X1 X2
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e159
                | exact resolve b26e159 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e159
              have b26e175 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e158 X0 X1
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e158
                | exact resolve b26e158 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e158
              have b26e189 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e21 X1 X0
                   have i₂ := b26e60 (σ X0) X2 (σ X1)
                   grind)
                | exact superpose b26e60 b26e21
                | (have j1 := b26e60 (σ X0) X2 (σ X1)
                   grind)
                | exact resolve b26e21 b26e60
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e60
              have b26e226 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 X0)) X1) ∨ (M.op X1 X1) = X1 ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X2) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e47 X0 X1 X1
                   have i₂ := b26e20 X0 X1
                   grind)
                | exact superpose b26e20 b26e47
                | (have j0 := b26e47 X1 X1 X2
                   have j1 := b26e20 X2 X0
                   grind)
                | exact resolve b26e47 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e47
              have b26e267 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X2) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e226 X0 X1 X2
                   have i₂ := b26e33 X0 X0
                   grind)
                | exact superpose b26e33 b26e226
                | (have j0 := b26e226 X0 X1 X2
                   grind)
                | exact resolve b26e226 b26e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e226
              have b26e301 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e18 X1 (σ X0)
                   have i₂ := b26e52 X0 X0
                   grind)
                | exact superpose b26e52 b26e18
                | (have j0 := b26e18 X1 (σ X0)
                   have j1 := b26e52 X0 X0
                   grind)
                | (have r₁ := b26e18 X0 (σ X0)
                   have r₂ := b26e52 X0 X1
                   grind)
                | (have r₁ := b26e18 X0 (σ X1)
                   have r₂ := b26e52 X1 X1
                   grind)
                | exact resolve b26e18 b26e52
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e327 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b26e52 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e52
              have b26e329 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b26e327 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e327
              have b26e341 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0 X1
                first
                | (have j0 := b26e301 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e301
              have b26e352 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
                intro X0 X1
                first
                | (have j0 := b26e341 X0 X1
                   have j1 := b26e18 X1 (σ X0)
                   grind)
                | (have r₁ := b26e341 X0 X1
                   have r₂ := b26e18 X0 (σ X0)
                   grind)
                | exact resolve b26e341 b26e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e341
              have b26e443 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e352 (τ X0) X1
                   have i₂ := b26e30 X0 (τ X0)
                   grind)
                | exact superpose b26e30 b26e352
                | (have j0 := b26e352 (τ X0) X1
                   grind)
                | exact resolve b26e352 b26e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e352
              have b26e454 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e443 X0 X1
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e443
                | (have j0 := b26e443 X0 X1
                   grind)
                | exact resolve b26e443 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e443
              have b26e461 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e454 X0 X1
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e454
                | (have j0 := b26e454 X0 X1
                   grind)
                | exact resolve b26e454 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e454
              have b26e479 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e461 (τ X0) X1
                   have i₂ := b26e139 X0 X0
                   grind)
                | exact superpose b26e139 b26e461
                | (have j0 := b26e461 (τ X0) X1
                   grind)
                | exact resolve b26e461 b26e139
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e139 b26e461
              have b26e914 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
                intro X0
                first
                | (have i₁ := b26e329 (τ X0)
                   have i₂ := b26e30 X0 (τ X0)
                   grind)
                | exact superpose b26e30 b26e329
                | (have j0 := b26e329 (τ X0)
                   grind)
                | exact resolve b26e329 b26e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e30 b26e329
              have b26e930 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
                intro X0
                first
                | (have i₁ := b26e914 X0
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e914
                | (have j0 := b26e914 X0
                   grind)
                | exact resolve b26e914 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e914
              have b26e939 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
                intro X0
                first
                | (have i₁ := b26e930 X0
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e930
                | (have j0 := b26e930 X0
                   grind)
                | exact resolve b26e930 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e930
              have b26e1451 : ∀ X0 : G, (k X0 (τ (σ (k y y)))) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
                intro X0
                first
                | (have i₁ := b26e175 X0 (σ y)
                   have i₂ := b26e151 y
                   grind)
                | exact superpose b26e151 b26e175
                | (have j1 := b26e151 y
                   grind)
                | exact resolve b26e175 b26e151
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e151 b26e175
              have b26e1473 : ∀ X0 : G, (k X0 (τ (σ (k y y)))) = X0 := by
                intro X0
                first
                | (have j0 := b26e1451 X0
                   grind)
                | (have r₁ := b26e1451 X0
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e1451 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1451
              have b26e1481 : ∀ X0 : G, (k X0 (k y y)) = X0 := by
                intro X0
                first
                | (have i₁ := b26e1473 X0
                   have i₂ := b26e16 (k y y)
                   grind)
                | exact superpose b26e16 b26e1473
                | exact resolve b26e1473 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1473
              have b26e1493 : (k y y) ≠ (k y y) ∨ (k y y) = (M.op (k y y) (k y y)) := by
                first
                | (have i₁ := b26e939 (k y y)
                   have i₂ := b26e1481 (k y y)
                   grind)
                | exact superpose b26e1481 b26e939
                | (have j0 := b26e939 (k y y)
                   grind)
                | (have r₁ := b26e939 (k y y)
                   have r₂ := b26e1481 (k y y)
                   grind)
                | exact resolve b26e939 b26e1481
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e939 b26e1481
              have b26e1509 : (k y y) = (M.op (k y y) (k y y)) := by grind
              clear b26e1493
              have b26e1586 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e64 X0 (σ X0)
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e64
                | (have j0 := b26e64 X1 X1
                   grind)
                | exact resolve b26e64 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e64
              have b26e1654 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e1586 X0 X1
                   have i₂ := b26e21 X0 X1
                   grind)
                | exact superpose b26e21 b26e1586
                | (have j0 := b26e1586 X1 X1
                   grind)
                | exact resolve b26e1586 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1586
              have b26e2533 : ∀ X0 : G, (M.op X0 (k y y)) = X0 := by
                intro X0
                first
                | (have i₁ := b26e33 (k y y) X0
                   have i₂ := b26e1509
                   grind)
                | exact superpose b26e1509 b26e33
                | exact resolve b26e33 b26e1509
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1509
              have b26e2931 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
                intro X0
                first
                | (have i₁ := b26e22
                   have i₂ := b26e189 x y X0
                   grind)
                | exact superpose b26e189 b26e22
                | (have j1 := b26e189 x y X0
                   grind)
                | exact resolve b26e22 b26e189
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e189
              have b26e3636 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
                intro X0
                first
                | (have j0 := b26e267 X0 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e267
              have b26e3637 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
                intro X0
                first
                | (have j0 := b26e3636 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e3636
              have b26e3638 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
                intro X0
                first
                | (have j0 := b26e3637 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e3637
              have b26e71413 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
                intro X0
                first
                | (have i₁ := b26e2931 X0
                   have i₂ := b26e1654 y x
                   grind)
                | exact superpose b26e1654 b26e2931
                | (have j0 := b26e2931 X0
                   have j1 := b26e1654 x x
                   grind)
                | (have r₁ := b26e2931 X0
                   have r₂ := b26e1654 y x
                   grind)
                | exact resolve b26e2931 b26e1654
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1654 b26e2931
              have b26e71414 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
                intro X0
                first
                | (have j0 := b26e71413 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e71413
              have b26e71419 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
                intro X0
                first
                | (have j0 := b26e71414 X0
                   grind)
                | (have r₁ := b26e71414 X0
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e71414 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e71414
              have b26e71424 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
                intro X0
                first
                | (have j0 := b26e71419 X0
                   grind)
                | (have r₁ := b26e71419 X0
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e71419 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e71419
              have b26e71624 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ y) (M.op (σ x) (σ x))))) = X0 ∨ (k X1 (σ x)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e174 X0 (σ y) (σ x)
                   have i₂ := b26e71424 X1
                   grind)
                | exact superpose b26e71424 b26e174
                | (have j1 := b26e71424 X1
                   grind)
                | exact resolve b26e174 b26e71424
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e174 b26e71424
              have b26e71670 : ∀ X0 X1 : G, (k X0 (τ (σ y))) = X0 ∨ (k X1 (σ x)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e71624 X0 X1
                   have i₂ := b26e33 (σ x) (σ y)
                   grind)
                | exact superpose b26e33 b26e71624
                | (have j0 := b26e71624 X0 X1
                   grind)
                | exact resolve b26e71624 b26e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e33 b26e71624
              have b26e71723 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ (k X1 (σ x)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e71670 X0 X1
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e71670
                | (have j0 := b26e71670 X0 X1
                   grind)
                | exact resolve b26e71670 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e71670
              have b26e73085 : ∀ X0 X1 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ (k X1 y) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e479 (σ x) X0
                   have i₂ := b26e71723 X1 (σ x)
                   grind)
                | exact superpose b26e71723 b26e479
                | (have j0 := b26e479 (σ x) X0
                   have j1 := b26e71723 X1 X1
                   grind)
                | exact resolve b26e479 b26e71723
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e479 b26e71723
              have b26e73214 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = X0 ∨ (k X1 y) = X1 := by
                intro X0 X1
                first
                | (have j0 := b26e73085 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e73085
              have b26e73258 : ∀ X0 X1 : G, (k X0 x) = X0 ∨ (k X1 y) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e73214 X0 X1
                   have i₂ := b26e16 x
                   grind)
                | exact superpose b26e16 b26e73214
                | (have j0 := b26e73214 X0 X1
                   grind)
                | exact resolve b26e73214 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e73214
              have b26e73424 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op x x) ∨ (k X0 y) = X0 := by
                intro X0
                first
                | (have i₁ := b26e3638 x
                   have i₂ := b26e73258 x X0
                   grind)
                | exact superpose b26e73258 b26e3638
                | (have j0 := b26e3638 x
                   have j1 := b26e73258 X0 X0
                   grind)
                | exact resolve b26e3638 b26e73258
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e3638 b26e73258
              have b26e73695 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 y) = X0 := by
                intro X0
                first
                | (have j0 := b26e73424 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e73424
              have b26e73759 : ∀ X0 : G, (k X0 y) = X0 := by
                intro X0
                first
                | (have j0 := b26e73695 X0
                   grind)
                | (have r₁ := b26e73695 X0
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e73695 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e73695
              have b26e74977 : ∀ X0 : G, (M.op X0 y) = X0 := by
                intro X0
                first
                | (have i₁ := b26e2533 X0
                   have i₂ := b26e73759 y
                   grind)
                | exact superpose b26e73759 b26e2533
                | exact resolve b26e2533 b26e73759
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2533 b26e73759
              have b26e76219 : y ≠ y := by
                first
                | (have i₁ := b26e23
                   have i₂ := b26e74977 y
                   grind)
                | exact superpose b26e74977 b26e23
                | (have r₁ := b26e23
                   have r₂ := b26e74977 y
                   grind)
                | exact resolve b26e23 b26e74977
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e74977
              have b26e76220 : False := by grind
              exact b26e76220

/-- `Equation727`: `x = y ◇ (y ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pxy_Equation727 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law727 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law727.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e58 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e60 : False := by grind
      exact b0e60
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
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
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X1) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e32 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 x y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X0 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X3 (M.op X1 (M.op (M.op X2 X1) X0)) X1
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) = (M.op X1 (M.op X1 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) X1 X2
               have i₂ := b4e13 X0 (M.op X2 X1) X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : x = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b4e32 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e32
            | exact resolve b4e32 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 : G, (M.op (M.op x (M.op y X0)) (M.op (M.op x (M.op y X0)) (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op x (M.op y X0)) x
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e13
            | exact resolve b4e13 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e78 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (σ X0) (σ X0)
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e13
            | exact resolve b4e13 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e92 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b4e33 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e33
            | exact resolve b4e33 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e109 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 (M.op X2 X0)) X1) (M.op (M.op (M.op X3 (M.op X2 X0)) X1) X5)) = (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X4 (M.op X0 (M.op X0 X1))) X5)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e35 X0 (M.op (M.op X3 (M.op X2 X1)) X0) (M.op X2 X1) X3
               have i₂ := b4e35 X0 X1 X2 X3
               grind)
            | exact superpose b4e35 b4e35
            | exact resolve b4e35 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e116 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X0 X3)) = (M.op (M.op (M.op X2 X1) X0) (M.op (M.op (M.op X2 X1) X0) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e35 X3 (M.op (M.op X2 X1) X0) X1 X1
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e35
            | exact resolve b4e35 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e124 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 (M.op X2 X0) x
               have i₂ := b4e35 X1 X0 X2 x
               grind)
            | exact superpose b4e35 b4e13
            | exact resolve b4e13 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e128 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op (M.op X3 (M.op X2 X0)) X1) (M.op (M.op (M.op X3 (M.op X2 X0)) X1) X5)) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5)) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b4e109 X0 X1 X2 X3 x X5
               have i₂ := b4e35 X5 (M.op X0 X1) X0 x
               grind)
            | exact superpose b4e35 b4e109
            | exact resolve b4e109 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109
          have b4e129 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5)) = (M.op (M.op (M.op X2 X0) (M.op (M.op X3 (M.op X2 X0)) X1)) (M.op X1 X5)) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b4e128 X0 X1 X2 X3 X5
               have i₂ := b4e116 X1 (M.op X2 X0) X3 X5
               grind)
            | exact superpose b4e116 b4e128
            | exact resolve b4e128 b4e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e128
          have b4e130 : ∀ X0 X1 X5 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5)) = (M.op (M.op X0 (M.op X0 X1)) (M.op X1 X5)) := by
            intro X0 X1 X5
            first
            | (have i₁ := b4e129 X0 X1 x x X5
               have i₂ := b4e35 X1 X0 x x
               grind)
            | exact superpose b4e35 b4e129
            | exact resolve b4e129 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129
          have b4e319 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op (σ x) X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e124 (σ x) X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e124
            | exact resolve b4e124 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e337 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (M.op X1 (σ x)) (M.op (σ x) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e124 (σ x) (M.op (σ x) (M.op (σ y) X0)) X1
               have i₂ := b4e33 X0
               grind)
            | exact superpose b4e33 b4e124
            | exact resolve b4e124 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e341 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b4e124 x (M.op x y) X0
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e124
            | exact resolve b4e124 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e342 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b4e124 y x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e124
            | exact resolve b4e124 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e343 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e124 X2 (M.op (M.op X3 X2) X0) X1
               have i₂ := b4e13 X0 X2 X3
               grind)
            | exact superpose b4e13 b4e124
            | exact resolve b4e124 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e345 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op X1 (σ x)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e124 (σ x) (M.op (σ y) X0) X1
               have i₂ := b4e33 X0
               grind)
            | exact superpose b4e33 b4e124
            | exact resolve b4e124 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e346 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e124 (σ x) (σ y) X0
               have i₂ := b4e92
               grind)
            | exact superpose b4e92 b4e124
            | exact resolve b4e124 b4e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e347 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e124 x (M.op y X0) X1
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e124
            | exact resolve b4e124 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e359 : (M.op x y) = (M.op y (M.op x x)) := by
            first
            | (have i₁ := b4e341 x
               have i₂ := b4e347 (M.op x x) x
               grind)
            | exact superpose b4e347 b4e341
            | exact resolve b4e341 b4e347
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e341
          have b4e362 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (σ y) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b4e337 X0 x
               have i₂ := b4e345 (M.op (σ x) X0) x
               grind)
            | exact superpose b4e345 b4e337
            | exact resolve b4e337 b4e345
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e337
          have b4e486 : ∀ X0 : G, (M.op (σ (M.op y y)) (M.op (σ (M.op y y)) (M.op (σ x) X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e78 (M.op y y) X0
               have i₂ := b4e342 y
               grind)
            | exact superpose b4e342 b4e78
            | exact resolve b4e78 b4e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e342
          have b4e496 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X2 X2)) X0) = (M.op (M.op X1 (σ X2)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e124 (σ X2) (M.op (σ (M.op X2 X2)) X0) X1
               have i₂ := b4e78 X2 X0
               grind)
            | exact superpose b4e78 b4e124
            | exact resolve b4e124 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e601 : (σ y) = (M.op (σ (M.op x x)) (σ x)) := by
            first
            | (have i₁ := b4e346 (σ x)
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e346
            | exact resolve b4e346 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e346
          have b4e733 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 (M.op (M.op X3 (M.op X4 X0)) X1)) X5) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e343 X5 X2 (M.op (M.op X3 (M.op X4 X0)) X1) (M.op X4 X0)
               have i₂ := b4e35 X1 X0 X4 X3
               grind)
            | exact superpose b4e35 b4e343
            | exact resolve b4e343 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e735 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e343 X3 X1 (M.op X2 (M.op X2 X0)) (M.op x X2)
               have i₂ := b4e124 X2 X0 x
               grind)
            | exact superpose b4e124 b4e343
            | exact resolve b4e343 b4e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e124 b4e343
          have b4e884 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x x)) X0) := by
            intro X0
            first
            | (have i₁ := b4e345 X0 (σ x)
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e345
            | exact resolve b4e345 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e345
          have b4e976 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op x (M.op y X1)) (M.op X1 X0)) (M.op X0 X2)) (M.op (M.op (M.op (M.op x (M.op y X1)) (M.op X1 X0)) (M.op X0 X2)) (M.op X2 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e34 X0 (M.op (M.op x (M.op y X0)) (M.op X0 X1)) (M.op x (M.op y X0)) X3
               have i₂ := b4e38 X0 X1
               grind)
            | exact superpose b4e38 b4e34
            | exact resolve b4e34 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e38
          have b4e989 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op (M.op x (M.op y X1)) (M.op X1 X0)) (M.op X0 X2))) (M.op (M.op X0 X2) (M.op X2 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e976 X0 X1 X2 X3
               have i₂ := b4e116 (M.op X0 X2) (M.op X1 X0) (M.op x (M.op y X1)) (M.op X2 X3)
               grind)
            | exact superpose b4e116 b4e976
            | exact resolve b4e976 b4e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e116 b4e976
          have b4e1034 : ∀ X0 X2 X3 : G, (M.op (M.op X0 (M.op X0 (M.op X0 X2))) (M.op (M.op X0 X2) (M.op X2 X3))) = X3 := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e989 X0 x X2 X3
               have i₂ := b4e733 X0 (M.op X0 X2) (M.op x X0) (M.op x (M.op y x)) x (M.op (M.op X0 X2) (M.op X2 X3))
               grind)
            | exact superpose b4e733 b4e989
            | exact resolve b4e989 b4e733
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e733 b4e989
          have b4e1060 : ∀ X0 X2 X3 : G, (M.op X2 (M.op (M.op X0 X2) (M.op X2 X3))) = X3 := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e1034 X0 X2 X3
               have i₂ := b4e735 X2 X0 X0 (M.op (M.op X0 X2) (M.op X2 X3))
               grind)
            | exact superpose b4e735 b4e1034
            | exact resolve b4e1034 b4e735
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e735 b4e1034
          have b4e1222 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (σ (M.op X1 X1)) X0)) = (M.op (σ X1) (M.op (M.op X2 (σ X1)) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e1060 X2 (σ X1) (M.op (σ X1) (M.op (σ (M.op X1 X1)) X0))
               have i₂ := b4e78 X1 X0
               grind)
            | exact superpose b4e78 b4e1060
            | exact resolve b4e1060 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e2132 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
            intro X0
            first
            | (have i₁ := b4e130 (σ x) (σ y) X0
               have i₂ := b4e92
               grind)
            | exact superpose b4e92 b4e130
            | exact resolve b4e130 b4e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92
          have b4e2246 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (σ (M.op y y)) (M.op (M.op (σ x) (σ y)) X0)) := by
            intro X0
            first
            | (have i₁ := b4e2132 X0
               have i₂ := b4e496 (M.op (M.op (σ x) (σ y)) X0) (σ x) y
               grind)
            | exact superpose b4e496 b4e2132
            | exact resolve b4e2132 b4e496
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2132
          have b4e2288 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (σ (M.op y y)) (M.op (σ (M.op y y)) X0)) := by
            intro X0
            first
            | (have i₁ := b4e2246 X0
               have i₂ := b4e496 X0 (σ x) y
               grind)
            | exact superpose b4e496 b4e2246
            | exact resolve b4e2246 b4e496
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2246
          have b4e2308 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) X0)) = (M.op (σ (M.op y y)) (M.op (σ (M.op y y)) X0)) := by
            intro X0
            first
            | (have i₁ := b4e2288 X0
               have i₂ := b4e362 X0
               grind)
            | exact superpose b4e362 b4e2288
            | exact resolve b4e2288 b4e362
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e362 b4e2288
          have b4e2327 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op (M.op x x) (M.op x x))) := by
            first
            | (have i₁ := b4e30 (M.op x x)
               have i₂ := b4e884 (σ (M.op x x))
               grind)
            | exact superpose b4e884 b4e30
            | exact resolve b4e30 b4e884
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e884
          have b4e2382 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op y (M.op x x))) := by
            first
            | (have i₁ := b4e2327
               have i₂ := b4e347 (M.op x x) x
               grind)
            | exact superpose b4e347 b4e2327
            | exact resolve b4e2327 b4e347
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e347 b4e2327
          have b4e2396 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b4e2382
               have i₂ := b4e359
               grind)
            | exact superpose b4e359 b4e2382
            | exact resolve b4e2382 b4e359
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e359 b4e2382
          have b4e3472 : (σ x) = (M.op (σ y) (M.op (σ x) (σ (M.op x x)))) := by
            first
            | (have i₁ := b4e319 (σ x)
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e319
            | exact resolve b4e319 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30
          have b4e3502 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) (M.op (M.op X1 (σ y)) (M.op (σ x) (M.op (σ x) X0)))) = (M.op (M.op X1 (M.op X1 (σ y))) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e130 X1 (σ y) (M.op (σ x) (M.op (σ x) X0))
               have i₂ := b4e319 X0
               grind)
            | exact superpose b4e319 b4e130
            | exact resolve b4e130 b4e319
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e319
          have b4e3508 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 (σ y))) X0) = (M.op (σ (M.op y y)) (M.op (M.op X1 (σ y)) (M.op (σ x) (M.op (σ x) X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e3502 X0 X1
               have i₂ := b4e496 (M.op (M.op X1 (σ y)) (M.op (σ x) (M.op (σ x) X0))) X1 y
               grind)
            | exact superpose b4e496 b4e3502
            | exact resolve b4e3502 b4e496
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3502
          have b4e3521 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 (σ y))) X0) = (M.op (σ (M.op y y)) (M.op (σ (M.op y y)) (M.op (σ x) (M.op (σ x) X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e3508 X0 X1
               have i₂ := b4e496 (M.op (σ x) (M.op (σ x) X0)) X1 y
               grind)
            | exact superpose b4e496 b4e3508
            | exact resolve b4e3508 b4e496
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3508
          have b4e3528 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X1 (M.op X1 (σ y))) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e3521 X0 X1
               have i₂ := b4e486 (M.op (σ x) X0)
               grind)
            | exact superpose b4e486 b4e3521
            | exact resolve b4e3521 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e486 b4e3521
          have b4e4322 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (M.op X0 (σ y)) (σ (M.op x x)))) = (M.op (M.op X0 (M.op X0 (σ y))) (σ (M.op x y))) := by
            intro X0
            first
            | (have i₁ := b4e130 X0 (σ y) (σ (M.op x x))
               have i₂ := b4e2396
               grind)
            | exact superpose b4e2396 b4e130
            | exact resolve b4e130 b4e2396
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130 b4e2396
          have b4e4329 : ∀ X0 : G, (M.op (σ x) (σ (M.op x y))) = (M.op (M.op X0 (σ y)) (M.op (M.op X0 (σ y)) (σ (M.op x x)))) := by
            intro X0
            first
            | (have i₁ := b4e4322 X0
               have i₂ := b4e3528 (σ (M.op x y)) X0
               grind)
            | exact superpose b4e3528 b4e4322
            | exact resolve b4e4322 b4e3528
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3528 b4e4322
          have b4e4345 : ∀ X0 : G, (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op y y)) (M.op (M.op X0 (σ y)) (σ (M.op x x)))) := by
            intro X0
            first
            | (have i₁ := b4e4329 X0
               have i₂ := b4e496 (M.op (M.op X0 (σ y)) (σ (M.op x x))) X0 y
               grind)
            | exact superpose b4e496 b4e4329
            | exact resolve b4e4329 b4e496
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4329
          have b4e4357 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op y y)) (M.op (σ (M.op y y)) (σ (M.op x x)))) := by
            first
            | (have i₁ := b4e4345 x
               have i₂ := b4e496 (σ (M.op x x)) x y
               grind)
            | exact superpose b4e496 b4e4345
            | exact resolve b4e4345 b4e496
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e496 b4e4345
          have b4e4363 : (M.op (σ y) (M.op (σ x) (σ (M.op x x)))) = (M.op (σ x) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e4357
               have i₂ := b4e2308 (σ (M.op x x))
               grind)
            | exact superpose b4e2308 b4e4357
            | exact resolve b4e4357 b4e2308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2308 b4e4357
          have b4e4368 : (σ x) = (M.op (σ x) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e4363
               have i₂ := b4e3472
               grind)
            | exact superpose b4e3472 b4e4363
            | exact resolve b4e4363 b4e3472
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3472 b4e4363
          have b4e4860 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (M.op X0 (σ x)) (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e1060 X0 (σ x) (σ (M.op x y))
               have i₂ := b4e4368
               grind)
            | exact superpose b4e4368 b4e1060
            | exact resolve b4e1060 b4e4368
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1060 b4e4368
          have b4e4863 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x x)) (σ x))) := by
            first
            | (have i₁ := b4e4860 x
               have i₂ := b4e1222 (σ x) x x
               grind)
            | exact superpose b4e1222 b4e4860
            | exact resolve b4e4860 b4e1222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1222 b4e4860
          have b4e4878 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e4863
               have i₂ := b4e601
               grind)
            | exact superpose b4e601 b4e4863
            | exact resolve b4e4863 b4e601
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e601 b4e4863
          have b4e4887 : False := by grind
          exact b4e4887
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X1) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e32 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X0 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X3 (M.op X1 (M.op (M.op X2 X1) X0)) X1
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) = (M.op X1 (M.op X1 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) X1 X2
               have i₂ := b5e13 X0 (M.op X2 X1) X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 X1 : G, (M.op (M.op x (M.op y X0)) (M.op (M.op x (M.op y X0)) (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (M.op x (M.op y X0)) x
               have i₂ := b5e32 X0
               grind)
            | exact superpose b5e32 b5e13
            | exact resolve b5e13 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e41 : x = y ∨ x = (k x y) := by grind
          clear b5e38
          have b5e42 : x = (k x y) := by
            first
            | (have r₁ := b5e41
               have r₂ := b5e21
               grind)
            | exact resolve b5e41 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b5e73 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (σ X0) (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e13
            | exact resolve b5e13 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e88 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 (M.op X2 X0)) X1) (M.op (M.op (M.op X3 (M.op X2 X0)) X1) X5)) = (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X4 (M.op X0 (M.op X0 X1))) X5)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e34 X0 (M.op (M.op X3 (M.op X2 X1)) X0) (M.op X2 X1) X3
               have i₂ := b5e34 X0 X1 X2 X3
               grind)
            | exact superpose b5e34 b5e34
            | exact resolve b5e34 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e89 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X2)) = (M.op (σ (M.op X0 X0)) (M.op (M.op X1 (σ (M.op X0 X0))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34 X0 (σ X0) (σ X0) x
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e34
            | exact resolve b5e34 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e90 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op (M.op x (M.op y X0)) (M.op (M.op x (M.op y X0)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34 X0 (M.op x (M.op y X0)) x x
               have i₂ := b5e32 X0
               grind)
            | exact superpose b5e32 b5e34
            | exact resolve b5e34 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e93 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X0 X3)) = (M.op (M.op (M.op X2 X1) X0) (M.op (M.op (M.op X2 X1) X0) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e34 X3 (M.op (M.op X2 X1) X0) X1 X1
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e34
            | exact resolve b5e34 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e94 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X1 X4)) = (M.op (M.op (M.op X2 (M.op X3 X0)) X1) (M.op (M.op X0 (M.op X0 X1)) X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e34 X4 X1 (M.op X2 (M.op X3 X0)) (M.op X3 X0)
               have i₂ := b5e34 X1 X0 X3 X2
               grind)
            | exact superpose b5e34 b5e34
            | exact resolve b5e34 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e95 : ∀ X0 X1 : G, (M.op (M.op x (M.op y X0)) (M.op X0 X1)) = (M.op (M.op y X0) (M.op (M.op y X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e34 X1 (M.op y X0) x x
               have i₂ := b5e32 X0
               grind)
            | exact superpose b5e32 b5e34
            | exact resolve b5e34 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e97 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X1 (M.op (M.op X4 (M.op X3 (M.op X0 X1))) X2))) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e34 (M.op (M.op X4 (M.op X3 (M.op X0 X1))) X2) X1 X0 X3
               have i₂ := b5e34 X2 (M.op X0 X1) X3 X4
               grind)
            | exact superpose b5e34 b5e34
            | exact resolve b5e34 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e99 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X0)) X1) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 X1)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op (M.op X3 (M.op X2 X0)) X1) X0 X2
               have i₂ := b5e34 X1 X0 X2 X3
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e100 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 (M.op X2 X0) x
               have i₂ := b5e34 X1 X0 X2 x
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e102 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 (M.op X3 X0)) X1) (M.op (M.op (M.op X2 (M.op X3 X0)) X1) (M.op (M.op X0 (M.op X0 X1)) X4))) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 X4 (M.op (M.op X2 (M.op X3 X0)) X1) (M.op X3 X0)
               have i₂ := b5e34 X1 X0 X3 X2
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e104 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op (M.op X3 (M.op X2 X0)) X1) (M.op (M.op (M.op X3 (M.op X2 X0)) X1) X5)) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5)) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b5e88 X0 X1 X2 X3 x X5
               have i₂ := b5e34 X5 (M.op X0 X1) X0 x
               grind)
            | exact superpose b5e34 b5e88
            | exact resolve b5e88 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e88
          have b5e105 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5)) = (M.op (M.op (M.op X2 X0) (M.op (M.op X3 (M.op X2 X0)) X1)) (M.op X1 X5)) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b5e104 X0 X1 X2 X3 X5
               have i₂ := b5e93 X1 (M.op X2 X0) X3 X5
               grind)
            | exact superpose b5e93 b5e104
            | exact resolve b5e104 b5e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e104
          have b5e106 : ∀ X0 X1 X5 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5)) = (M.op (M.op X0 (M.op X0 X1)) (M.op X1 X5)) := by
            intro X0 X1 X5
            first
            | (have i₁ := b5e105 X0 X1 x x X5
               have i₂ := b5e34 X1 X0 x x
               grind)
            | exact superpose b5e34 b5e105
            | exact resolve b5e105 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e105
          have b5e119 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X2 (M.op X3 X0)) X1) (M.op (M.op X0 (M.op X0 X1)) X4)) (M.op (M.op (M.op (M.op X2 (M.op X3 X0)) X1) (M.op (M.op X0 (M.op X0 X1)) X4)) (M.op X4 X5))) = X5 := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e33 X0 (M.op (M.op X3 (M.op X2 X1)) X0) (M.op X2 X1) X3
               have i₂ := b5e34 X0 X1 X2 X3
               grind)
            | exact superpose b5e34 b5e33
            | exact resolve b5e33 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e132 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (M.op X2 X1) (σ X0))) (M.op (M.op X1 (M.op (M.op X2 X1) (σ X0))) (σ (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33 (σ X0) X1 X2 (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e33
            | exact resolve b5e33 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e137 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X3) X0) = (M.op X3 (M.op X3 (M.op (M.op X2 (M.op (M.op X1 X2) X3)) (M.op X3 X0)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e34 (M.op (M.op X2 (M.op (M.op X1 X2) X3)) (M.op X3 X0)) X3 (M.op X1 X2) X2
               have i₂ := b5e33 X3 X2 X1 X0
               grind)
            | exact superpose b5e33 b5e34
            | exact resolve b5e34 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e139 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op (M.op X2 X1) X3)) (M.op X3 X0)) (M.op (M.op (M.op X1 (M.op (M.op X2 X1) X3)) (M.op X3 X0)) X5)) = (M.op X0 (M.op (M.op X4 X0) X5)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e34 X0 (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X0 X3)) (M.op X1 (M.op (M.op X2 X1) X0)) X3
               have i₂ := b5e33 X0 X1 X2 X3
               grind)
            | exact superpose b5e33 b5e34
            | exact resolve b5e34 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e143 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op X4 X0) X5)) = (M.op (M.op (M.op (M.op X2 X1) X3) (M.op (M.op X1 (M.op (M.op X2 X1) X3)) (M.op X3 X0))) (M.op (M.op X3 X0) X5)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e139 X0 X1 X2 X3 X4 X5
               have i₂ := b5e93 (M.op X3 X0) (M.op (M.op X2 X1) X3) X1 X5
               grind)
            | exact superpose b5e93 b5e139
            | exact resolve b5e139 b5e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e139
          have b5e153 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X3 X0)) X1) (M.op (M.op X0 (M.op X0 X1)) X4))) (M.op (M.op (M.op X0 (M.op X0 X1)) X4) (M.op X4 X5))) = X5 := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e119 X0 X1 X2 X3 X4 X5
               have i₂ := b5e93 (M.op (M.op X0 (M.op X0 X1)) X4) X1 (M.op X2 (M.op X3 X0)) (M.op X4 X5)
               grind)
            | exact superpose b5e93 b5e119
            | exact resolve b5e119 b5e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e119
          have b5e156 : ∀ X0 X3 X4 X5 : G, (M.op X0 (M.op (M.op X4 X0) X5)) = (M.op (M.op X3 (M.op X3 (M.op X3 X0))) (M.op (M.op X3 X0) X5)) := by
            intro X0 X3 X4 X5
            first
            | (have i₁ := b5e143 X0 x x X3 X4 X5
               have i₂ := b5e34 (M.op X3 X0) X3 (M.op x x) x
               grind)
            | exact superpose b5e34 b5e143
            | exact resolve b5e143 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e143
          have b5e163 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X1 (M.op X1 (M.op X1 X4))) (M.op (M.op (M.op X0 (M.op X0 X1)) X4) (M.op X4 X5))) = X5 := by
            intro X0 X1 X4 X5
            first
            | (have i₁ := b5e153 X0 X1 x x X4 X5
               have i₂ := b5e94 X0 X1 x x X4
               grind)
            | exact superpose b5e94 b5e153
            | exact resolve b5e153 b5e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e94 b5e153
          have b5e166 : ∀ X0 X3 X4 X5 : G, (M.op X0 (M.op (M.op X4 X0) X5)) = (M.op (M.op X3 (M.op X3 X0)) (M.op (M.op X3 (M.op X3 X0)) X5)) := by
            intro X0 X3 X4 X5
            first
            | (have i₁ := b5e156 X0 X3 X4 X5
               have i₂ := b5e106 X3 (M.op X3 X0) X5
               grind)
            | exact superpose b5e106 b5e156
            | exact resolve b5e156 b5e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e156
          have b5e218 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X1) (σ X0)
               have i₂ := b5e45 X0 X1
               grind)
            | exact superpose b5e45 b5e17
            | (have j0 := b5e17 (σ X0) (σ X1)
               have j1 := b5e45 X0 X1
               grind)
            | (have r₁ := b5e17 (σ X0) (σ X1)
               have r₂ := b5e45 X0 X1
               grind)
            | exact resolve b5e17 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e219 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (σ X1) (M.op (σ (k X0 X1)) X2))) = X2 ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 (σ X1) (σ X0)
               have i₂ := b5e45 X0 X1
               grind)
            | exact superpose b5e45 b5e13
            | (have j1 := b5e45 X0 X1
               grind)
            | exact resolve b5e13 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e229 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e218 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e218
          have b5e234 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e229 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e229
            | (have j0 := b5e229 X0 X1
               grind)
            | exact resolve b5e229 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e229
          have b5e284 : ∀ X0 X1 : G, (M.op x (M.op y X0)) = (M.op (M.op X1 x) (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e100 x (M.op x (M.op y X0)) X1
               have i₂ := b5e32 X0
               grind)
            | exact superpose b5e32 b5e100
            | exact resolve b5e100 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e286 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b5e100 y x X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e100
            | exact resolve b5e100 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e287 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e100 X2 (M.op (M.op X3 X2) X0) X1
               have i₂ := b5e13 X0 X2 X3
               grind)
            | exact superpose b5e13 b5e100
            | exact resolve b5e100 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e289 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e100 x (M.op y X0) X1
               have i₂ := b5e32 X0
               grind)
            | exact superpose b5e32 b5e100
            | exact resolve b5e100 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e302 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e284 X0 x
               have i₂ := b5e289 (M.op x X0) x
               grind)
            | exact superpose b5e289 b5e284
            | exact resolve b5e284 b5e289
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e284 b5e289
          have b5e391 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X2 X2)) X0) = (M.op (M.op X1 (σ X2)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e100 (σ X2) (M.op (σ (M.op X2 X2)) X0) X1
               have i₂ := b5e73 X2 X0
               grind)
            | exact superpose b5e73 b5e100
            | exact resolve b5e100 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e660 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 (M.op (M.op X3 (M.op X4 X0)) X1)) X5) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e287 X5 X2 (M.op (M.op X3 (M.op X4 X0)) X1) (M.op X4 X0)
               have i₂ := b5e34 X1 X0 X4 X3
               grind)
            | exact superpose b5e34 b5e287
            | exact resolve b5e287 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e662 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e287 X3 X1 (M.op X2 (M.op X2 X0)) (M.op x X2)
               have i₂ := b5e100 X2 X0 x
               grind)
            | exact superpose b5e100 b5e287
            | exact resolve b5e287 b5e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e796 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op x (M.op y X1)) (M.op X1 X0)) (M.op X0 X2)) (M.op (M.op (M.op (M.op x (M.op y X1)) (M.op X1 X0)) (M.op X0 X2)) (M.op X2 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e33 X0 (M.op (M.op x (M.op y X0)) (M.op X0 X1)) (M.op x (M.op y X0)) X3
               have i₂ := b5e37 X0 X1
               grind)
            | exact superpose b5e37 b5e33
            | exact resolve b5e33 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33 b5e37
          have b5e809 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op (M.op x (M.op y X1)) (M.op X1 X0)) (M.op X0 X2))) (M.op (M.op X0 X2) (M.op X2 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e796 X0 X1 X2 X3
               have i₂ := b5e93 (M.op X0 X2) (M.op X1 X0) (M.op x (M.op y X1)) (M.op X2 X3)
               grind)
            | exact superpose b5e93 b5e796
            | exact resolve b5e796 b5e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e796
          have b5e847 : ∀ X0 X2 X3 : G, (M.op (M.op X0 (M.op X0 (M.op X0 X2))) (M.op (M.op X0 X2) (M.op X2 X3))) = X3 := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e809 X0 x X2 X3
               have i₂ := b5e660 X0 (M.op X0 X2) (M.op x X0) (M.op x (M.op y x)) x (M.op (M.op X0 X2) (M.op X2 X3))
               grind)
            | exact superpose b5e660 b5e809
            | exact resolve b5e809 b5e660
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e809
          have b5e867 : ∀ X0 X2 X3 : G, (M.op X2 (M.op (M.op X0 X2) (M.op X2 X3))) = X3 := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e847 X0 X2 X3
               have i₂ := b5e662 X2 X0 X0 (M.op (M.op X0 X2) (M.op X2 X3))
               grind)
            | exact superpose b5e662 b5e847
            | exact resolve b5e847 b5e662
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e662 b5e847
          have b5e893 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op y X0)) X2) = (M.op (M.op y (M.op x X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e287 X2 X1 (M.op y X0) x
               have i₂ := b5e302 X0
               grind)
            | exact superpose b5e302 b5e287
            | exact resolve b5e287 b5e302
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e302
          have b5e982 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X4 X3) X0)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e99 X3 (M.op (M.op X4 X3) X0) X2 X1
               have i₂ := b5e13 X0 X3 X4
               grind)
            | exact superpose b5e13 b5e99
            | exact resolve b5e99 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1203 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (σ (M.op X1 X1)) X0)) = (M.op (σ X1) (M.op (M.op X2 (σ X1)) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e867 X2 (σ X1) (M.op (σ X1) (M.op (σ (M.op X1 X1)) X0))
               have i₂ := b5e73 X1 X0
               grind)
            | exact superpose b5e73 b5e867
            | exact resolve b5e867 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e867
          have b5e1426 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x (M.op y X2)) (M.op (M.op X0 (M.op X1 X2)) X3)) = (M.op (M.op y X2) (M.op (M.op y X2) (M.op X2 (M.op X2 (M.op X2 X3))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e95 X2 (M.op X2 (M.op X2 (M.op X2 X3)))
               have i₂ := b5e99 X2 X3 X1 X0
               grind)
            | exact superpose b5e99 b5e95
            | exact resolve b5e95 b5e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95
          have b5e1522 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x (M.op y X2)) (M.op (M.op X0 (M.op X1 X2)) X3)) = (M.op (M.op y X2) (M.op X2 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e1426 X0 X1 X2 X3
               have i₂ := b5e100 X2 (M.op X2 X3) y
               grind)
            | exact superpose b5e100 b5e1426
            | exact resolve b5e1426 b5e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1426
          have b5e1545 : ∀ X0 X1 X2 X3 : G, (M.op (M.op y (M.op x X2)) (M.op (M.op X0 (M.op X1 X2)) X3)) = (M.op (M.op y X2) (M.op X2 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e1522 X0 X1 X2 X3
               have i₂ := b5e893 X2 x (M.op (M.op X0 (M.op X1 X2)) X3)
               grind)
            | exact superpose b5e893 b5e1522
            | exact resolve b5e1522 b5e893
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1522
          have b5e1750 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2)) = (M.op (M.op X3 (M.op X0 X1)) (M.op X1 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e287 (M.op X1 X2) X0 (M.op X0 X1) X3
               have i₂ := b5e106 X0 X1 X2
               grind)
            | exact superpose b5e106 b5e287
            | exact resolve b5e287 b5e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e287
          have b5e2608 : ∀ X0 X1 : G, (M.op (σ (M.op y y)) (M.op (σ (M.op y y)) X0)) = (M.op (σ x) (M.op (M.op X1 (σ x)) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e89 (M.op y y) X1 x
               have i₂ := b5e286 y
               grind)
            | exact superpose b5e286 b5e89
            | exact resolve b5e89 b5e286
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2684 : ∀ X0 : G, (M.op (σ (M.op y y)) (M.op (σ (M.op y y)) X0)) = (M.op (σ x) (M.op (σ (M.op x x)) X0)) := by
            intro X0
            first
            | (have i₁ := b5e2608 X0 x
               have i₂ := b5e1203 X0 x x
               grind)
            | exact superpose b5e1203 b5e2608
            | exact resolve b5e2608 b5e1203
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1203 b5e2608
          have b5e2824 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4)) = (M.op (M.op x (M.op y X3)) (M.op (M.op x (M.op y X3)) (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4))))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e90 X3 X2 (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4)))
               have i₂ := b5e99 (M.op X2 X3) X4 X1 X0
               grind)
            | exact superpose b5e99 b5e90
            | exact resolve b5e90 b5e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2921 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) (M.op X0 (M.op (M.op X1 X0) X2))) = (M.op X0 (M.op X0 (M.op (M.op x (M.op y X0)) X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34 (M.op (M.op x (M.op y X0)) X2) X0 y x
               have i₂ := b5e90 X0 X1 X2
               grind)
            | exact superpose b5e90 b5e34
            | exact resolve b5e34 b5e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90
          have b5e2970 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) (M.op X0 (M.op (M.op X1 X0) X2))) = (M.op X0 (M.op X0 (M.op (M.op y (M.op x X0)) X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e2921 X0 X1 X2
               have i₂ := b5e893 X0 x X2
               grind)
            | exact superpose b5e893 b5e2921
            | exact resolve b5e2921 b5e893
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2921
          have b5e3053 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4)) = (M.op (M.op y (M.op x X3)) (M.op (M.op x (M.op y X3)) (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4))))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e2824 X0 X1 X2 X3 X4
               have i₂ := b5e893 X3 x (M.op (M.op x (M.op y X3)) (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4))))
               grind)
            | exact superpose b5e893 b5e2824
            | exact resolve b5e2824 b5e893
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e893 b5e2824
          have b5e3172 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4)) = (M.op (M.op y X3) (M.op X3 (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4))))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e3053 X0 X1 X2 X3 X4
               have i₂ := b5e1545 x y X3 (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4)))
               grind)
            | exact superpose b5e1545 b5e3053
            | exact resolve b5e3053 b5e1545
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1545 b5e3053
          have b5e3244 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4)) = (M.op X3 (M.op X3 (M.op (M.op y (M.op x X3)) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4))))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e3172 X0 X1 X2 X3 X4
               have i₂ := b5e2970 X3 X2 (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4))
               grind)
            | exact superpose b5e2970 b5e3172
            | exact resolve b5e3172 b5e2970
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2970 b5e3172
          have b5e3287 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4)) = (M.op X3 (M.op X3 (M.op X3 (M.op X3 (M.op (M.op X2 X3) X4))))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e3244 X0 X1 X2 X3 X4
               have i₂ := b5e982 (M.op (M.op X2 X3) X4) y x X3 X2
               grind)
            | exact superpose b5e982 b5e3244
            | exact resolve b5e3244 b5e982
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e982 b5e3244
          have b5e3297 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 X4)) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e3287 X0 X1 X2 X3 X4
               have i₂ := b5e13 X4 X3 X2
               grind)
            | exact superpose b5e13 b5e3287
            | exact resolve b5e3287 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3287
          have b5e4721 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 (M.op X1 X2)) X3) (M.op X3 X0)) (M.op (M.op X4 (M.op (M.op (M.op X1 (M.op X1 X2)) X3) (M.op X3 X0))) X5)) = (M.op (M.op (M.op X2 (M.op X2 (M.op X2 X3))) X0) (M.op (M.op (M.op X2 (M.op X2 (M.op X2 X3))) X0) X5)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e166 (M.op (M.op (M.op X0 (M.op X0 X1)) X4) (M.op X4 X5)) (M.op X1 (M.op X1 (M.op X1 X4))) X4 X5
               have i₂ := b5e163 X0 X1 X4 X5
               grind)
            | exact superpose b5e163 b5e166
            | exact resolve b5e166 b5e163
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e163 b5e166
          have b5e5052 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 (M.op X1 X2)) X3) (M.op X3 X0)) (M.op (M.op X4 (M.op (M.op (M.op X1 (M.op X1 X2)) X3) (M.op X3 X0))) X5)) = (M.op (M.op (M.op X2 (M.op X2 X3)) (M.op (M.op X2 (M.op X2 (M.op X2 X3))) X0)) (M.op X0 X5)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e4721 X0 X1 X2 X3 X4 X5
               have i₂ := b5e93 X0 (M.op X2 (M.op X2 X3)) X2 X5
               grind)
            | exact superpose b5e93 b5e4721
            | exact resolve b5e4721 b5e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4721
          have b5e5223 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 (M.op X1 X2)) X3) (M.op X3 X0)) (M.op (M.op X4 (M.op (M.op (M.op X1 (M.op X1 X2)) X3) (M.op X3 X0))) X5)) = (M.op (M.op (M.op X2 X3) (M.op (M.op X2 X3) X0)) (M.op X0 X5)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e5052 X0 X1 X2 X3 X4 X5
               have i₂ := b5e660 (M.op X2 X3) X0 (M.op X2 (M.op X2 X3)) X2 X2 (M.op X0 X5)
               grind)
            | exact superpose b5e660 b5e5052
            | exact resolve b5e5052 b5e660
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e660 b5e5052
          have b5e5318 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 (M.op X1 X2)) X3) (M.op X3 X0)) (M.op (M.op X4 (M.op (M.op (M.op X1 (M.op X1 X2)) X3) (M.op X3 X0))) X5)) = (M.op (M.op (M.op X2 X3) X0) (M.op (M.op (M.op X2 X3) X0) X5)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e5223 X0 X1 X2 X3 X4 X5
               have i₂ := b5e1750 (M.op X2 X3) X0 X5 (M.op X2 X3)
               grind)
            | exact superpose b5e1750 b5e5223
            | exact resolve b5e5223 b5e1750
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1750 b5e5223
          have b5e5349 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 (M.op X1 X2)) X3) (M.op X3 X0)) (M.op (M.op X4 (M.op (M.op (M.op X1 (M.op X1 X2)) X3) (M.op X3 X0))) X5)) = (M.op (M.op X3 (M.op (M.op X2 X3) X0)) (M.op X0 X5)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e5318 X0 X1 X2 X3 X4 X5
               have i₂ := b5e93 X0 X3 X2 X5
               grind)
            | exact superpose b5e93 b5e5318
            | exact resolve b5e5318 b5e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5318
          have b5e5357 : ∀ X0 X2 X3 X5 : G, (M.op (M.op X3 X0) (M.op (M.op X3 X0) X5)) = (M.op (M.op X3 (M.op (M.op X2 X3) X0)) (M.op X0 X5)) := by
            intro X0 X2 X3 X5
            first
            | (have i₁ := b5e5349 X0 x X2 X3 x X5
               have i₂ := b5e34 X5 (M.op X3 X0) (M.op (M.op x (M.op x X2)) X3) x
               grind)
            | exact superpose b5e34 b5e5349
            | exact resolve b5e5349 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e5349
          have b5e5539 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X1 (σ (M.op y y))) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e391 X0 X1 (M.op y y)
               have i₂ := b5e286 y
               grind)
            | exact superpose b5e286 b5e391
            | exact resolve b5e391 b5e286
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e6125 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X0 X1) X2)) (M.op X2 X3)) = (M.op (M.op X4 X2) (M.op (M.op (M.op X0 X1) X2) X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e100 X2 (M.op (M.op X1 (M.op (M.op X0 X1) X2)) (M.op X2 X3)) X4
               have i₂ := b5e137 X3 X0 X1 X2
               grind)
            | exact superpose b5e137 b5e100
            | exact resolve b5e100 b5e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e137
          have b5e8993 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X5 (M.op (M.op X1 X0) X2))) X3) = (M.op (M.op (M.op X1 X0) X2) (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op X2 X3)))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e99 (M.op (M.op X1 X0) X2) X3 X5 X4
               have i₂ := b5e93 X2 X0 X1 X3
               grind)
            | exact superpose b5e93 b5e99
            | exact resolve b5e99 b5e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e93
          have b5e9064 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op (M.op X4 (M.op X5 (M.op (M.op X1 X0) X2))) X3) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e8993 X0 X1 X2 X3 X4 X5
               have i₂ := b5e13 (M.op X2 X3) (M.op (M.op X1 X0) X2) X0
               grind)
            | exact superpose b5e13 b5e8993
            | exact resolve b5e8993 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8993
          have b5e9801 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X1 (M.op X2 (M.op (M.op X3 (M.op X4 X5)) X6))) (M.op (M.op X5 (M.op X5 X6)) X0)) = (M.op (M.op (M.op X3 (M.op X4 X5)) X6) (M.op (M.op (M.op X3 (M.op X4 X5)) X6) X0)) := by
            intro X0 X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b5e99 (M.op (M.op X3 (M.op X4 X5)) X6) (M.op (M.op X5 (M.op X5 X6)) X0) X2 X1
               have i₂ := b5e102 X5 X6 X3 X4 X0
               grind)
            | exact superpose b5e102 b5e99
            | exact resolve b5e99 b5e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e102
          have b5e9868 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X1 (M.op X2 (M.op (M.op X3 (M.op X4 X5)) X6))) (M.op (M.op X5 (M.op X5 X6)) X0)) = (M.op (M.op (M.op X4 X5) (M.op (M.op X3 (M.op X4 X5)) X6)) (M.op X6 X0)) := by
            intro X0 X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b5e9801 X0 X1 X2 X3 X4 X5 X6
               have i₂ := b5e6125 X3 (M.op X4 X5) X6 X0 (M.op X3 (M.op X4 X5))
               grind)
            | exact superpose b5e6125 b5e9801
            | exact resolve b5e9801 b5e6125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9801
          have b5e10150 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X1 (M.op X2 (M.op (M.op X3 (M.op X4 X5)) X6))) (M.op (M.op X5 (M.op X5 X6)) X0)) = (M.op (M.op (M.op X4 X5) X6) (M.op (M.op (M.op X4 X5) X6) X0)) := by
            intro X0 X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b5e9868 X0 X1 X2 X3 X4 X5 X6
               have i₂ := b5e5357 X6 X3 (M.op X4 X5) X0
               grind)
            | exact superpose b5e5357 b5e9868
            | exact resolve b5e9868 b5e5357
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9868
          have b5e10377 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X1 (M.op X2 (M.op (M.op X3 (M.op X4 X5)) X6))) (M.op (M.op X5 (M.op X5 X6)) X0)) = (M.op (M.op X5 (M.op (M.op X4 X5) X6)) (M.op X6 X0)) := by
            intro X0 X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b5e10150 X0 X1 X2 X3 X4 X5 X6
               have i₂ := b5e6125 X4 X5 X6 X0 (M.op X4 X5)
               grind)
            | exact superpose b5e6125 b5e10150
            | exact resolve b5e10150 b5e6125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6125 b5e10150
          have b5e10585 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X1 (M.op X2 (M.op (M.op X3 (M.op X4 X5)) X6))) (M.op (M.op X5 (M.op X5 X6)) X0)) = (M.op (M.op X5 X6) (M.op (M.op X5 X6) X0)) := by
            intro X0 X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b5e10377 X0 X1 X2 X3 X4 X5 X6
               have i₂ := b5e5357 X6 X4 X5 X0
               grind)
            | exact superpose b5e5357 b5e10377
            | exact resolve b5e10377 b5e5357
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5357 b5e10377
          have b5e10738 : ∀ X0 X5 X6 : G, (M.op X6 (M.op (M.op X5 (M.op X5 X6)) X0)) = (M.op (M.op X5 X6) (M.op (M.op X5 X6) X0)) := by
            intro X0 X5 X6
            first
            | (have i₁ := b5e10585 X0 x x x x X5 X6
               have i₂ := b5e9064 (M.op x X5) x X6 (M.op (M.op X5 (M.op X5 X6)) X0) x x
               grind)
            | exact superpose b5e9064 b5e10585
            | exact resolve b5e10585 b5e9064
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9064 b5e10585
          have b5e16006 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X5 (M.op X6 (M.op X3 X0))) X4) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X0))) (M.op (M.op X3 X0) X4)))) := by
            intro X0 X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b5e99 (M.op X3 X0) X4 X6 X5
               have i₂ := b5e97 X3 X0 (M.op (M.op X3 X0) X4) X2 X1
               grind)
            | exact superpose b5e97 b5e99
            | exact resolve b5e99 b5e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e97
          have b5e16101 : ∀ X0 X3 X4 X5 X6 : G, (M.op (M.op X5 (M.op X6 (M.op X3 X0))) X4) = (M.op X0 (M.op X0 (M.op X0 (M.op (M.op X3 X0) X4)))) := by
            intro X0 X3 X4 X5 X6
            first
            | (have i₁ := b5e16006 X0 x x X3 X4 X5 X6
               have i₂ := b5e3297 x x X3 X0 (M.op (M.op X3 X0) X4)
               grind)
            | exact superpose b5e3297 b5e16006
            | exact resolve b5e16006 b5e3297
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16006
          have b5e16497 : ∀ X0 X3 X4 X5 X6 : G, (M.op X0 X4) = (M.op (M.op X5 (M.op X6 (M.op X3 X0))) X4) := by
            intro X0 X3 X4 X5 X6
            first
            | (have i₁ := b5e16101 X0 X3 X4 X5 X6
               have i₂ := b5e13 X4 X0 X3
               grind)
            | exact superpose b5e13 b5e16101
            | exact resolve b5e16101 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16101
          have b5e20765 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X1) = (M.op (M.op X2 (M.op X3 (σ (M.op X0 X0)))) X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e16497 (σ X0) (σ X0) X1 X2 X3
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e16497
            | exact resolve b5e16497 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16497
          have b5e23493 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e219 x y X0
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e219
            | (have j0 := b5e219 x y x
               grind)
            | exact resolve b5e219 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e219
          have b5e23617 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b5e23493 X0
               grind)
            | (have r₁ := b5e23493 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e23493 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23493
          have b5e23658 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
            intro X0
            first
            | (have j0 := b5e23617 X0
               grind)
            | (have r₁ := b5e23617 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e23617 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23617
          have b5e23717 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x x)) X0)) = (M.op (σ y) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e23658 (M.op (σ x) (M.op (σ (M.op x x)) X0))
               have i₂ := b5e73 x X0
               grind)
            | exact superpose b5e73 b5e23658
            | exact resolve b5e23658 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e23729 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X1 (σ y)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e100 (σ y) (M.op (σ x) X0) X1
               have i₂ := b5e23658 X0
               grind)
            | exact superpose b5e23658 b5e100
            | exact resolve b5e100 b5e23658
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e100
          have b5e23821 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y y)) X0) := by
            intro X0
            first
            | (have i₁ := b5e23729 X0 x
               have i₂ := b5e391 X0 x y
               grind)
            | exact superpose b5e391 b5e23729
            | exact resolve b5e23729 b5e391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23729
          have b5e24179 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 (σ (M.op y y))) X1)) = (M.op (σ y) (M.op (σ y) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e89 y X0 X1
               have i₂ := b5e23821 (M.op (M.op X0 (σ (M.op y y))) X1)
               grind)
            | exact superpose b5e23821 b5e89
            | exact resolve b5e89 b5e23821
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e89
          have b5e24180 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ x) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e30 (M.op y y)
               have i₂ := b5e23821 (σ (M.op y y))
               grind)
            | exact superpose b5e23821 b5e30
            | exact resolve b5e30 b5e23821
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e24201 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (σ (M.op y y)))) X0) = (M.op (σ (M.op y y)) (M.op (σ (M.op y y)) (M.op (σ (M.op y y)) (M.op (σ x) X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e99 (σ (M.op y y)) X0 X2 X1
               have i₂ := b5e23821 X0
               grind)
            | exact superpose b5e23821 b5e99
            | exact resolve b5e99 b5e23821
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e24345 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (σ (M.op y y)))) X0) = (M.op (σ x) (M.op (σ (M.op x x)) (M.op (σ (M.op y y)) (M.op (σ x) X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e24201 X0 X1 X2
               have i₂ := b5e2684 (M.op (σ (M.op y y)) (M.op (σ x) X0))
               grind)
            | exact superpose b5e2684 b5e24201
            | exact resolve b5e24201 b5e2684
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2684 b5e24201
          have b5e24351 : (σ x) = (M.op (σ x) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e24180
               have i₂ := b5e286 y
               grind)
            | exact superpose b5e286 b5e24180
            | exact resolve b5e24180 b5e286
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e286 b5e24180
          have b5e24352 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) X1)) = (M.op (σ y) (M.op (σ y) X1)) := by
            intro X1
            first
            | (have i₁ := b5e24179 x X1
               have i₂ := b5e5539 X1 x
               grind)
            | exact superpose b5e5539 b5e24179
            | exact resolve b5e24179 b5e5539
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5539 b5e24179
          have b5e24407 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (σ (M.op y y)))) X0) = (M.op (σ y) (M.op (σ y) (M.op (σ (M.op y y)) (M.op (σ x) X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e24345 X0 X1 X2
               have i₂ := b5e23717 (M.op (σ (M.op y y)) (M.op (σ x) X0))
               grind)
            | exact superpose b5e23717 b5e24345
            | exact resolve b5e24345 b5e23717
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23717 b5e24345
          have b5e24462 : ∀ X0 X1 X2 : G, (M.op (σ x) X0) = (M.op (M.op X1 (M.op X2 (σ (M.op y y)))) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e24407 X0 X1 X2
               have i₂ := b5e73 y (M.op (σ x) X0)
               grind)
            | exact superpose b5e73 b5e24407
            | exact resolve b5e24407 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73 b5e24407
          have b5e24500 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e24462 X0 x x
               have i₂ := b5e20765 y X0 x x
               grind)
            | exact superpose b5e20765 b5e24462
            | exact resolve b5e24462 b5e20765
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20765 b5e24462
          have b5e24570 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e234 x y
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e234
            | (have j0 := b5e234 x y
               grind)
            | exact resolve b5e234 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e234
          have b5e24573 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
          clear b5e24570
          have b5e24577 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e24573
               have r₂ := b5e23
               grind)
            | exact resolve b5e24573 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24573
          have b5e24586 : (σ y) = (σ (k y x)) := by
            first
            | (have r₁ := b5e24577
               have r₂ := b5e24
               grind)
            | exact resolve b5e24577 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24577
          have b5e24604 : (M.op (σ y) (σ y)) = (σ (M.op (k y x) (k y x))) := by
            first
            | (have i₁ := b5e30 (k y x)
               have i₂ := b5e24586
               grind)
            | exact superpose b5e24586 b5e30
            | exact resolve b5e30 b5e24586
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e24621 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op (M.op X1 X0) (σ y))) (M.op (M.op X0 (M.op (M.op X1 X0) (σ y))) (σ (M.op (k y x) (k y x))))) := by
            intro X0 X1
            first
            | (have i₁ := b5e132 (k y x) X1 x
               have i₂ := b5e24586
               grind)
            | exact superpose b5e24586 b5e132
            | exact resolve b5e132 b5e24586
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e132 b5e24586
          have b5e24630 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X1 X0) (σ y)) (M.op (M.op X0 (M.op X0 (M.op (M.op X1 X0) (σ y)))) (σ (M.op (k y x) (k y x))))) := by
            intro X0 X1
            first
            | (have i₁ := b5e24621 X0 X1
               have i₂ := b5e10738 (σ (M.op (k y x) (k y x))) X0 (M.op (M.op X1 X0) (σ y))
               grind)
            | exact superpose b5e10738 b5e24621
            | exact resolve b5e24621 b5e10738
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24621
          have b5e24642 : (σ (M.op y y)) = (σ (M.op (k y x) (k y x))) := by
            first
            | (have i₁ := b5e24604
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e24604
            | exact resolve b5e24604 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e24604
          have b5e24650 : ∀ X0 X1 : G, (σ y) = (M.op (σ (M.op y y)) (M.op (M.op X0 (M.op X0 (M.op (M.op X1 X0) (σ y)))) (σ (M.op (k y x) (k y x))))) := by
            intro X0 X1
            first
            | (have i₁ := b5e24630 X0 X1
               have i₂ := b5e391 (M.op (M.op X0 (M.op X0 (M.op (M.op X1 X0) (σ y)))) (σ (M.op (k y x) (k y x)))) (M.op X1 X0) y
               grind)
            | exact superpose b5e391 b5e24630
            | exact resolve b5e24630 b5e391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e391 b5e24630
          have b5e24654 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (M.op X0 (M.op (M.op X1 X0) (σ y)))) (σ (M.op (k y x) (k y x))))) := by
            intro X0 X1
            first
            | (have i₁ := b5e24650 X0 X1
               have i₂ := b5e23821 (M.op (M.op X0 (M.op X0 (M.op (M.op X1 X0) (σ y)))) (σ (M.op (k y x) (k y x))))
               grind)
            | exact superpose b5e23821 b5e24650
            | exact resolve b5e24650 b5e23821
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23821 b5e24650
          have b5e24655 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (M.op X0 (M.op (M.op X1 X0) (σ y)))) (σ (M.op (k y x) (k y x))))) := by
            intro X0 X1
            first
            | (have i₁ := b5e24654 X0 X1
               have i₂ := b5e24500 (M.op (M.op X0 (M.op X0 (M.op (M.op X1 X0) (σ y)))) (σ (M.op (k y x) (k y x))))
               grind)
            | exact superpose b5e24500 b5e24654
            | exact resolve b5e24654 b5e24500
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24654
          have b5e24656 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op (k y x) (k y x))))) := by
            first
            | (have i₁ := b5e24655 x x
               have i₂ := b5e3297 x x (M.op x x) (σ y) (σ (M.op (k y x) (k y x)))
               grind)
            | exact superpose b5e3297 b5e24655
            | exact resolve b5e24655 b5e3297
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3297 b5e24655
          have b5e24657 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
            first
            | (have i₁ := b5e24656
               have i₂ := b5e24642
               grind)
            | exact superpose b5e24642 b5e24656
            | exact resolve b5e24656 b5e24642
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24642 b5e24656
          have b5e25191 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (σ x))) X0) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ y) X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e99 (σ x) X0 X2 X1
               have i₂ := b5e24500 X0
               grind)
            | exact superpose b5e24500 b5e99
            | exact resolve b5e99 b5e24500
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e99
          have b5e25334 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (σ x))) X0) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (M.op (σ y) X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e25191 X0 X1 X2
               have i₂ := b5e24352 (M.op (σ x) (M.op (σ y) X0))
               grind)
            | exact superpose b5e24352 b5e25191
            | exact resolve b5e25191 b5e24352
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24352 b5e25191
          have b5e25396 : ∀ X0 X1 X2 : G, (M.op (σ y) X0) = (M.op (M.op X1 (M.op X2 (σ x))) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e25334 X0 X1 X2
               have i₂ := b5e23658 (M.op (σ y) X0)
               grind)
            | exact superpose b5e23658 b5e25334
            | exact resolve b5e25334 b5e23658
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23658 b5e25334
          have b5e26619 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (M.op X0 (σ x)) (σ (M.op y y)))) = (M.op (M.op X0 (M.op X0 (σ x))) (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e106 X0 (σ x) (σ (M.op y y))
               have i₂ := b5e24351
               grind)
            | exact superpose b5e24351 b5e106
            | exact resolve b5e106 b5e24351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e106 b5e24351
          have b5e26662 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 (σ x)) (M.op (M.op X0 (σ x)) (σ (M.op y y)))) := by
            intro X0
            first
            | (have i₁ := b5e26619 X0
               have i₂ := b5e25396 (σ x) X0 X0
               grind)
            | exact superpose b5e25396 b5e26619
            | exact resolve b5e26619 b5e25396
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26619
          have b5e26697 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (M.op X0 (M.op X0 (σ x))) (σ (M.op y y)))) := by
            intro X0
            first
            | (have i₁ := b5e26662 X0
               have i₂ := b5e10738 (σ (M.op y y)) X0 (σ x)
               grind)
            | exact superpose b5e10738 b5e26662
            | exact resolve b5e26662 b5e10738
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10738 b5e26662
          have b5e26724 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (M.op X0 (M.op X0 (σ x))) (σ (M.op y y)))) := by
            intro X0
            first
            | (have i₁ := b5e26697 X0
               have i₂ := b5e24500 (M.op (M.op X0 (M.op X0 (σ x))) (σ (M.op y y)))
               grind)
            | exact superpose b5e24500 b5e26697
            | exact resolve b5e26697 b5e24500
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24500 b5e26697
          have b5e26744 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
            first
            | (have i₁ := b5e26724 x
               have i₂ := b5e25396 (σ (M.op y y)) x x
               grind)
            | exact superpose b5e25396 b5e26724
            | exact resolve b5e26724 b5e25396
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25396 b5e26724
          have b5e26760 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e26744
               have i₂ := b5e24657
               grind)
            | exact superpose b5e24657 b5e26744
            | exact resolve b5e26744 b5e24657
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24657 b5e26744
          have b5e26772 : False := by grind
          exact b5e26772
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X1) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e32 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) = (M.op X1 (M.op X1 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) X1 X2
               have i₂ := b7e13 X0 (M.op X2 X1) X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
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
          have b7e44 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e42
          have b7e45 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e44
               have r₂ := b7e23
               grind)
            | exact resolve b7e44 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e46 : (σ x) = (σ (k x y)) := by
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
          have b7e49 : (k x y) = (τ (σ x)) := by
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
          have b7e50 : x = (k x y) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e49
            | exact resolve b7e49 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e60 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e61 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e60
               have r₂ := b7e22
               grind)
            | exact resolve b7e60 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e63 : x = (M.op x y) := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e21
               grind)
            | exact resolve b7e61 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e89 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b7e32 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e32
            | exact resolve b7e32 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e114 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 (M.op X2 X0) x
               have i₂ := b7e34 X1 X0 X2 x
               grind)
            | exact superpose b7e34 b7e13
            | exact resolve b7e13 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e371 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b7e114 x y X0
               have i₂ := b7e63
               grind)
            | exact superpose b7e63 b7e114
            | exact resolve b7e114 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e376 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op X1 (σ x)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e114 (σ x) (M.op (σ y) X0) X1
               have i₂ := b7e32 X0
               grind)
            | exact superpose b7e32 b7e114
            | exact resolve b7e114 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e377 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e114 (σ x) (σ y) X0
               have i₂ := b7e89
               grind)
            | exact superpose b7e89 b7e114
            | exact resolve b7e114 b7e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e114
          have b7e737 : (σ y) = (M.op (σ (M.op x x)) (σ x)) := by
            first
            | (have i₁ := b7e377 (σ x)
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e377
            | exact resolve b7e377 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e377
          have b7e1363 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x x)) X0) := by
            intro X0
            first
            | (have i₁ := b7e376 X0 (σ x)
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e376
            | exact resolve b7e376 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e376
          have b7e1475 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op (M.op x x) (M.op x x))) := by
            first
            | (have i₁ := b7e30 (M.op x x)
               have i₂ := b7e1363 (σ (M.op x x))
               grind)
            | exact superpose b7e1363 b7e30
            | exact resolve b7e30 b7e1363
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1363
          have b7e1518 : (σ y) = (M.op (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e1475
               have i₂ := b7e371 x
               grind)
            | exact superpose b7e371 b7e1475
            | exact resolve b7e1475 b7e371
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e371 b7e1475
          have b7e1571 : (σ (M.op x x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b7e32 (σ (M.op x x))
               have i₂ := b7e1518
               grind)
            | exact superpose b7e1518 b7e32
            | exact resolve b7e32 b7e1518
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e1518
          have b7e1596 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e1571
               have i₂ := b7e89
               grind)
            | exact superpose b7e89 b7e1571
            | exact resolve b7e1571 b7e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89 b7e1571
          have b7e1657 : (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e737
               have i₂ := b7e1596
               grind)
            | exact superpose b7e1596 b7e737
            | exact resolve b7e737 b7e1596
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e737
          have b7e1659 : (τ (σ x)) = (M.op x x) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e1596
               grind)
            | exact superpose b7e1596 b7e14
            | exact resolve b7e14 b7e1596
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1596
          have b7e1692 : x = (M.op x x) := by
            first
            | (have i₁ := b7e1659
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1659
            | exact resolve b7e1659 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1659
          have b7e1693 : (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e1657
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e1657
            | exact resolve b7e1657 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e1657
          have b7e1695 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e1693
               have i₂ := b7e1692
               grind)
            | exact superpose b7e1692 b7e1693
            | exact resolve b7e1693 b7e1692
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1692 b7e1693
          have b7e1697 : False := by grind
          exact b7e1697
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e156 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e55 x y
               grind)
            | exact superpose b8e55 b8e20
            | (have j1 := b8e55 x y
               grind)
            | exact resolve b8e20 b8e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e177 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e156
               have r₂ := b8e24
               grind)
            | exact resolve b8e156 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156
          have b8e186 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e177
               have r₂ := b8e23
               grind)
            | exact resolve b8e177 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e177
          have b8e191 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e186
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e186
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e186
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e186
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e186 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e186
          have b8e192 : y = (M.op y x) ∨ x = y := by grind
          clear b8e191
          have b8e193 : x = y := by
            first
            | (have r₁ := b8e192
               have r₂ := b8e22
               grind)
            | exact resolve b8e192 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e192
          have b8e194 : False := by grind
          exact b8e194

/-- `Equation834`: `x = x ◇ ((y ◇ x) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_y_pxy_Equation834 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law834 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law834.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e67 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e71 : False := by grind
      exact b0e71
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
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
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X0 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e40 : ∀ X0 : G, y = (M.op y (M.op x (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b5e13 y x X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 (M.op (M.op x X0) (M.op X0 x))
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e45 : y = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b5e40 (M.op (M.op x y) (M.op y x))
               have i₂ := b5e13 y x x
               grind)
            | exact superpose b5e13 b5e40
            | exact resolve b5e40 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e48 : y = (M.op y x) := by
            first
            | (have i₁ := b5e45
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e45
            | exact resolve b5e45 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e50 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e55 : x = y ∨ y = (k x y) := by grind
          clear b5e50
          have b5e56 : y = (k x y) := by
            first
            | (have r₁ := b5e55
               have r₂ := b5e21
               grind)
            | exact resolve b5e55 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e63 : y ≠ y ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b5e17 y x
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e17
            | (have j0 := b5e17 x y
               grind)
            | (have r₁ := b5e17 y x
               have r₂ := b5e48
               grind)
            | exact resolve b5e17 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e66 : x = y ∨ x = (k y x) := by grind
          clear b5e63
          have b5e67 : x = (k y x) := by
            first
            | (have r₁ := b5e66
               have r₂ := b5e21
               grind)
            | exact resolve b5e66 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66
          have b5e120 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (σ X0) (σ X0) X1
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e144 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (M.op (σ (k X0 X1)) (M.op (σ X1) X2))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (σ X1) (σ X0) X2
               have i₂ := b5e59 X0 X1
               grind)
            | exact superpose b5e59 b5e13
            | (have j1 := b5e59 X0 X1
               grind)
            | exact resolve b5e13 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e145 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e59 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e633 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (k X0 X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e120 X0 (σ X1)
               have i₂ := b5e59 X0 X1
               grind)
            | exact superpose b5e59 b5e120
            | (have j1 := b5e59 X0 X1
               grind)
            | exact resolve b5e120 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e120
          have b5e2040 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e144 x y X0
               have i₂ := b5e56
               grind)
            | exact superpose b5e56 b5e144
            | (have j0 := b5e144 x y x
               grind)
            | exact resolve b5e144 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56 b5e144
          have b5e2099 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) X0))) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b5e2040 X0
               grind)
            | (have r₁ := b5e2040 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e2040 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2040
          have b5e2106 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) X0))) := by
            intro X0
            first
            | (have j0 := b5e2099 X0
               grind)
            | (have r₁ := b5e2099 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e2099 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2099
          have b5e2264 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e2106 (M.op (σ y) x)
               have i₂ := b5e2106 x
               grind)
            | exact superpose b5e2106 b5e2106
            | exact resolve b5e2106 b5e2106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2106
          have b5e2291 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e2264
               have i₂ := b5e31 y
               grind)
            | exact superpose b5e31 b5e2264
            | exact resolve b5e2264 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e2264
          have b5e24674 : (σ y) = (M.op (σ y) (M.op (σ (M.op y y)) (σ x))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e633 y x
               have i₂ := b5e67
               grind)
            | exact superpose b5e67 b5e633
            | (have j0 := b5e633 y x
               grind)
            | exact resolve b5e633 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e633
          have b5e24816 : (σ y) = (M.op (σ y) (M.op (σ (M.op y y)) (σ x))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e24674
               have r₂ := b5e23
               grind)
            | exact resolve b5e24674 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24674
          have b5e24899 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e24816
               have i₂ := b5e2291
               grind)
            | exact superpose b5e2291 b5e24816
            | exact resolve b5e24816 b5e2291
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2291 b5e24816
          have b5e25085 : (σ y) = (M.op (σ y) (σ (k y x))) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e24899
               have i₂ := b5e59 y x
               grind)
            | exact superpose b5e59 b5e24899
            | (have j1 := b5e59 y (k y x)
               grind)
            | exact resolve b5e24899 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59 b5e24899
          have b5e25158 : (σ y) = (M.op (σ y) (σ (k y x))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have j1 := b5e145 y x
               grind)
            | (have r₁ := b5e25085
               have r₂ := b5e145 y x
               grind)
            | exact resolve b5e25085 b5e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e145 b5e25085
          have b5e25159 : (σ y) = (M.op (σ y) (σ (k y x))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e25158
               have r₂ := b5e23
               grind)
            | exact resolve b5e25158 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25158
          have b5e25160 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e25159
               have i₂ := b5e67
               grind)
            | exact superpose b5e67 b5e25159
            | exact resolve b5e25159 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67 b5e25159
          have b5e25161 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear b5e25160
          have b5e25220 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b5e43 (σ x) (σ y)
               have i₂ := b5e25161
               grind)
            | exact superpose b5e25161 b5e43
            | exact resolve b5e43 b5e25161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e25269 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e25220
               have i₂ := b5e25161
               grind)
            | exact superpose b5e25161 b5e25220
            | exact resolve b5e25220 b5e25161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25161 b5e25220
          have b5e25284 : False := by grind
          exact b5e25284
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
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X0 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e36 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 (M.op (M.op x X0) (M.op X0 x))
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b7e36 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e36
            | exact resolve b7e36 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e44 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e37
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e37
            | exact resolve b7e37 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e45 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e50 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e45
          have b7e51 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e50
               have r₂ := b7e23
               grind)
            | exact resolve b7e50 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e52 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e51
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e51
            | exact resolve b7e51 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e55 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e52
               grind)
            | exact superpose b7e52 b7e14
            | exact resolve b7e14 b7e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e56 : y = (k x y) := by
            first
            | (have i₁ := b7e55
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e55
            | exact resolve b7e55 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e65 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e56
               grind)
            | exact superpose b7e56 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e66 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e22
               grind)
            | exact resolve b7e65 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e68 : y = (M.op x y) := by
            first
            | (have r₁ := b7e66
               have r₂ := b7e21
               grind)
            | exact resolve b7e66 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e82 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) y)) := by
            intro X0
            first
            | (have i₁ := b7e13 x X0 y
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e13
            | exact resolve b7e13 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e83 : ∀ X0 : G, y = (M.op y (M.op y (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b7e13 y x X0
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e13
            | exact resolve b7e13 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e133 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e17 (σ y) (σ x)
               have i₂ := b7e44
               grind)
            | exact superpose b7e44 b7e17
            | (have j0 := b7e17 (σ x) (σ y)
               grind)
            | (have r₁ := b7e17 (σ y) (σ x)
               have r₂ := b7e44
               grind)
            | exact resolve b7e17 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e137 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
          clear b7e133
          have b7e139 : (σ x) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b7e137
               have r₂ := b7e23
               grind)
            | exact resolve b7e137 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e137
          have b7e141 : (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b7e139
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e139
            | exact resolve b7e139 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e139
          have b7e175 : (k y x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e141
               grind)
            | exact superpose b7e141 b7e14
            | exact resolve b7e14 b7e141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e141
          have b7e176 : x = (k y x) := by
            first
            | (have i₁ := b7e175
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e175
            | exact resolve b7e175 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e175
          have b7e205 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 y x
               have i₂ := b7e176
               grind)
            | exact superpose b7e176 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e176
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e176
          have b7e206 : y = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e205
               have r₂ := b7e21
               grind)
            | exact resolve b7e205 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e205
          have b7e276 : y = (M.op y y) := by
            first
            | (have i₁ := b7e83 (M.op y x)
               have i₂ := b7e83 x
               grind)
            | exact superpose b7e83 b7e83
            | exact resolve b7e83 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e487 : x = (M.op x (M.op y y)) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e82 y
               have i₂ := b7e206
               grind)
            | exact superpose b7e206 b7e82
            | exact resolve b7e82 b7e206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e206
          have b7e499 : x = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e487
               have i₂ := b7e276
               grind)
            | exact superpose b7e276 b7e487
            | exact resolve b7e487 b7e276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e276 b7e487
          have b7e500 : x = (M.op y x) := by
            first
            | (have r₁ := b7e499
               have r₂ := b7e22
               grind)
            | exact resolve b7e499 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e499
          have b7e538 : x = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b7e82 y
               have i₂ := b7e500
               grind)
            | exact superpose b7e500 b7e82
            | exact resolve b7e82 b7e500
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82 b7e500
          have b7e548 : x = (M.op x y) := by
            first
            | (have i₁ := b7e538
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e538
            | exact resolve b7e538 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68 b7e538
          have b7e550 : False := by grind
          exact b7e550
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e91 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e100 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e91
               have r₂ := b8e24
               grind)
            | exact resolve b8e91 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91
          have b8e104 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e100
               have r₂ := b8e23
               grind)
            | exact resolve b8e100 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e100
          have b8e105 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e104
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e104
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e104
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e104
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e104 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104
          have b8e106 : x = (M.op x y) ∨ x = y := by grind
          clear b8e105
          have b8e107 : x = y := by
            first
            | (have r₁ := b8e106
               have r₂ := b8e22
               grind)
            | exact resolve b8e106 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106
          have b8e108 : False := by grind
          exact b8e108

/-- `Equation839`: `x = x ◇ ((y ◇ x) ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_x_pxy_Equation839 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law839 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law839.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e87 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e93 : False := by grind
      exact b0e93
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
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
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : (σ y) ≠ (σ y) := by
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e42 : ∀ X0 : G, (M.op X0 (M.op (M.op y X0) y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 (M.op X0 X1) (M.op X1 (M.op (M.op X0 X1) X2))
               have i₂ := b5e13 (M.op (M.op X0 X1) X2) X1 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e47 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e50 : x = y ∨ x = (k x y) := by grind
          clear b5e47
          have b5e51 : x = (k x y) := by
            first
            | (have r₁ := b5e50
               have r₂ := b5e21
               grind)
            | exact resolve b5e50 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e67 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e44 X0 (M.op (M.op x x) X0) X1
               have i₂ := b5e44 x x X0
               grind)
            | exact superpose b5e44 b5e44
            | exact resolve b5e44 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e102 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (M.op (M.op y X0) y) X0) := by
            intro X0
            first
            | (have i₁ := b5e67 X0 (M.op (M.op y X0) y)
               have i₂ := b5e42 X0
               grind)
            | exact superpose b5e42 b5e67
            | exact resolve b5e67 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e345 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (M.op (σ (k X0 X1)) (M.op X2 (σ X0)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (σ X1) (σ X0) X2
               have i₂ := b5e54 X0 X1
               grind)
            | exact superpose b5e54 b5e13
            | (have j1 := b5e54 X0 X1
               grind)
            | exact resolve b5e13 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e12380 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ x) (M.op X0 (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e345 x y X0
               have i₂ := b5e51
               grind)
            | exact superpose b5e51 b5e345
            | (have j0 := b5e345 x y x
               grind)
            | exact resolve b5e345 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51 b5e345
          have b5e12517 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ x) (M.op X0 (σ x)))) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b5e12380 X0
               grind)
            | (have r₁ := b5e12380 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e12380 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12380
          have b5e12533 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ x) (M.op X0 (σ x)))) := by
            intro X0
            first
            | (have j0 := b5e12517 X0
               grind)
            | (have r₁ := b5e12517 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e12517 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12517
          have b5e12540 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e12533 x
               have i₂ := b5e67 x (σ x)
               grind)
            | exact superpose b5e67 b5e12533
            | exact resolve b5e12533 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12533
          have b5e12552 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e54 y x
               have i₂ := b5e12540
               grind)
            | exact superpose b5e12540 b5e54
            | (have j0 := b5e54 y (k y x)
               grind)
            | exact resolve b5e54 b5e12540
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54 b5e12540
          have b5e12609 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
          clear b5e12552
          have b5e12633 : (σ y) = (σ (k y x)) := by
            first
            | (have r₁ := b5e12609
               have r₂ := b5e23
               grind)
            | exact resolve b5e12609 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12609
          have b5e12979 : (k y x) = (τ (σ y)) := by
            first
            | (have i₁ := b5e14 (k y x)
               have i₂ := b5e12633
               grind)
            | exact superpose b5e12633 b5e14
            | exact resolve b5e14 b5e12633
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12633
          have b5e13031 : y = (k y x) := by
            first
            | (have i₁ := b5e12979
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e12979
            | exact resolve b5e12979 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12979
          have b5e13580 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b5e18 y x
               have i₂ := b5e13031
               grind)
            | exact superpose b5e13031 b5e18
            | (have j0 := b5e18 y x
               grind)
            | exact resolve b5e18 b5e13031
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13031
          have b5e13587 : x = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b5e13580
               have r₂ := b5e21
               grind)
            | exact resolve b5e13580 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13580
          have b5e14167 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b5e102 x
               have i₂ := b5e13587
               grind)
            | exact superpose b5e13587 b5e102
            | exact resolve b5e102 b5e13587
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e102 b5e13587
          have b5e14243 : y = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b5e14167
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e14167
            | exact resolve b5e14167 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14167
          have b5e14244 : y = (M.op y x) := by grind
          clear b5e14243
          have b5e14427 : x = (M.op x y) := by
            first
            | (have i₁ := b5e67 y x
               have i₂ := b5e14244
               grind)
            | exact superpose b5e14244 b5e67
            | exact resolve b5e67 b5e14244
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67 b5e14244
          have b5e14480 : x = y := by
            first
            | (have i₁ := b5e14427
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e14427
            | exact resolve b5e14427 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14427
          have b5e14501 : False := by grind
          exact b5e14501
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
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b7e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b7e35 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) X0) (σ y))) = X0 := by
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
          have b7e37 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 (M.op X0 X1) (M.op X1 (M.op (M.op X0 X1) X2))
               have i₂ := b7e13 (M.op (M.op X0 X1) X2) X1 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e40 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e37 X0 (M.op (M.op x x) X0) X1
               have i₂ := b7e37 x x X0
               grind)
            | exact superpose b7e37 b7e37
            | exact resolve b7e37 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e45 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e48 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e45
          have b7e49 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e48
               have r₂ := b7e23
               grind)
            | exact resolve b7e48 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e50 : (σ x) = (σ (k x y)) := by
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
          have b7e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b7e63 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
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
          have b7e64 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e22
               grind)
            | exact resolve b7e63 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e66 : x = (M.op x y) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e21
               grind)
            | exact resolve b7e64 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e70 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e27 X0 X1
               have i₂ := b7e18 (τ X0) X1
               grind)
            | exact superpose b7e18 b7e27
            | (have j1 := b7e18 (τ X0) X1
               grind)
            | exact resolve b7e27 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e90 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k X0 (τ X1))
               have i₂ := b7e28 X1 X0
               grind)
            | exact superpose b7e28 b7e14
            | exact resolve b7e14 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e405 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (M.op (σ (k X0 X1)) (M.op X2 (σ X0)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 (σ X1) (σ X0) X2
               have i₂ := b7e58 X0 X1
               grind)
            | exact superpose b7e58 b7e13
            | (have j1 := b7e58 X0 X1
               grind)
            | exact resolve b7e13 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e7199 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (τ X0)))) ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e70 X0 (M.op X0 (τ X0))
               have i₂ := b7e40 X0 (τ X0)
               grind)
            | exact superpose b7e40 b7e70
            | (have j0 := b7e70 X0 (M.op X1 (τ X0))
               grind)
            | exact resolve b7e70 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e7224 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (τ X0)))) ∨ (τ X0) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e7199 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7199
          have b7e7264 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (τ X0)))) = X0 ∨ (τ X0) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e7224 X0 X1
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e7224
            | (have j0 := b7e7224 X0 X1
               grind)
            | exact resolve b7e7224 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7224
          have b7e21119 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X1 (τ (σ X0)))))) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e90 X0 (σ (M.op X1 (τ (σ X0))))
               have i₂ := b7e7264 (σ X0) X1
               grind)
            | exact superpose b7e7264 b7e90
            | (have j1 := b7e7264 (σ X0) X1
               grind)
            | exact resolve b7e90 b7e7264
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90 b7e7264
          have b7e21144 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op X1 (τ (σ X0)))) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e21119 X0 X1
               have i₂ := b7e14 (M.op X1 (τ (σ X0)))
               grind)
            | exact superpose b7e14 b7e21119
            | (have j0 := b7e21119 X0 X1
               grind)
            | exact resolve b7e21119 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21119
          have b7e21175 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e21144 X0 X1
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e21144
            | (have j0 := b7e21144 X0 X1
               grind)
            | exact resolve b7e21144 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21144
          have b7e21191 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e21175 X0 X1
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e21175
            | (have j0 := b7e21175 X0 X1
               grind)
            | exact resolve b7e21175 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21175
          have b7e21294 : y = (k y x) ∨ x = y := by
            first
            | (have i₁ := b7e21191 y x
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e21191
            | exact resolve b7e21191 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66 b7e21191
          have b7e21343 : y = (k y x) := by
            first
            | (have r₁ := b7e21294
               have r₂ := b7e21
               grind)
            | exact resolve b7e21294 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21294
          have b7e21408 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ y) (M.op X0 (σ y)))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b7e405 y x X0
               have i₂ := b7e21343
               grind)
            | exact superpose b7e21343 b7e405
            | (have j0 := b7e405 y x x
               grind)
            | exact resolve b7e405 b7e21343
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e405 b7e21343
          have b7e21423 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ y) (M.op X0 (σ y)))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            intro X0
            first
            | (have j0 := b7e21408 X0
               grind)
            | (have r₁ := b7e21408 X0
               have r₂ := b7e23
               grind)
            | exact resolve b7e21408 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21408
          have b7e21428 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e21423 x
               have i₂ := b7e40 x (σ y)
               grind)
            | exact superpose b7e40 b7e21423
            | exact resolve b7e21423 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40 b7e21423
          have b7e21430 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e21428
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e21428
            | exact resolve b7e21428 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21428
          have b7e21432 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b7e21430
               have r₂ := b7e23
               grind)
            | exact resolve b7e21430 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21430
          have b7e21925 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b7e35 (σ x)
               have i₂ := b7e21432
               grind)
            | exact superpose b7e21432 b7e35
            | exact resolve b7e35 b7e21432
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35 b7e21432
          have b7e22025 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e21925
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e21925
            | exact resolve b7e21925 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21925
          have b7e22032 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e22025
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e22025
            | exact resolve b7e22025 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e22025
          have b7e22034 : False := by grind
          exact b7e22034
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e268 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e53 x y
               grind)
            | exact superpose b8e53 b8e20
            | (have j1 := b8e53 x y
               grind)
            | exact resolve b8e20 b8e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e286 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e268
               have r₂ := b8e24
               grind)
            | exact resolve b8e268 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e268
          have b8e292 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e286
               have r₂ := b8e23
               grind)
            | exact resolve b8e286 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e286
          have b8e295 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e292
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e292
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e292
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e292
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e292 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e292
          have b8e296 : y = (M.op x y) ∨ x = y := by grind
          clear b8e295
          have b8e297 : x = y := by
            first
            | (have r₁ := b8e296
               have r₂ := b8e22
               grind)
            | exact resolve b8e296 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e296
          have b8e298 : False := by grind
          exact b8e298
