import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3331`: `x ◇ y = x ◇ (z ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_x_pxy_Equation3331 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3331 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3331.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e77 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e81 : False := by grind
      exact b0e81
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op y x) (M.op y y) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op y x) = (M.op y y) := by grind
          have b4e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e39 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X2 X1 (M.op X0 X1)
               have i₂ := b4e13 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e109 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op y y) y)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 x (M.op y y)
               have i₂ := b4e39 (M.op y y)
               grind)
            | exact superpose b4e39 b4e13
            | exact resolve b4e13 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e116 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b4e109 X0
               have i₂ := b4e41 y y X0
               grind)
            | exact superpose b4e41 b4e109
            | exact resolve b4e109 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109
          have b4e130 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e41 (σ y) (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e41
            | exact resolve b4e41 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e145 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e130 X0
               have i₂ := b4e41 (σ y) (σ y) X0
               grind)
            | exact superpose b4e41 b4e130
            | exact resolve b4e130 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e130
          have b4e163 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e30 x
               have i₂ := b4e145 (σ x)
               grind)
            | exact superpose b4e145 b4e30
            | exact resolve b4e30 b4e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e145
          have b4e164 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e163
               have i₂ := b4e116 x
               grind)
            | exact superpose b4e116 b4e163
            | exact resolve b4e163 b4e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e116 b4e163
          have b4e169 : False := by grind
          exact b4e169
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : (M.op y x) = (M.op y y) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e39 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x (M.op y y))) := by
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
          have b5e41 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 X1 (M.op X0 X1)
               have i₂ := b5e13 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e57 : (M.op y y) ≠ (M.op y y) ∨ x = y ∨ x = (k x y) := by
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
          have b5e62 : x = y ∨ x = (k x y) := by grind
          clear b5e57
          have b5e63 : x = (k x y) := by
            first
            | (have r₁ := b5e62
               have r₂ := b5e21
               grind)
            | exact resolve b5e62 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e70 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e17 X1 X0
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e17 X1 X1
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e17
            | (have j0 := b5e17 X0 X0
               have j1 := b5e18 X1 X0
               grind)
            | (have r₁ := b5e17 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e17 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | (have r₁ := b5e17 X0 X1
               have r₂ := b5e18 (M.op X1 X0) (M.op X1 X1)
               grind)
            | exact resolve b5e17 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e70 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70
          have b5e82 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e81 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e78 X0 X1
               have i₂ := b5e30 X1
               grind)
            | exact superpose b5e30 b5e78
            | (have j0 := b5e78 X0 X1
               grind)
            | exact resolve b5e78 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e103 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op y y) y)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x (M.op y y)
               have i₂ := b5e39 (M.op y y)
               grind)
            | exact superpose b5e39 b5e13
            | exact resolve b5e13 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e110 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b5e103 X0
               have i₂ := b5e41 y y X0
               grind)
            | exact superpose b5e41 b5e103
            | exact resolve b5e103 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e103
          have b5e525 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e83 y x
               grind)
            | exact superpose b5e83 b5e20
            | (have j1 := b5e83 y x
               grind)
            | exact resolve b5e20 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e554 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have r₁ := b5e525
               have r₂ := b5e23
               grind)
            | exact resolve b5e525 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e525
          have b5e580 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have i₁ := b5e554
               have i₂ := b5e110 x
               grind)
            | exact superpose b5e110 b5e554
            | exact resolve b5e554 b5e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e110 b5e554
          have b5e581 : (M.op (σ y) (σ x)) = (σ (k y x)) := by grind
          clear b5e580
          have b5e607 : (M.op (σ y) (σ y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e581
               grind)
            | exact superpose b5e581 b5e24
            | exact resolve b5e24 b5e581
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e608 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ (k y x)))) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 (σ y) (σ x)
               have i₂ := b5e581
               grind)
            | exact superpose b5e581 b5e13
            | exact resolve b5e13 b5e581
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e621 : (σ (M.op y y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b5e607
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e607
            | exact resolve b5e607 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e607
          have b5e672 : (σ (M.op y y)) ≠ (σ (M.op y x)) ∨ y = (k y x) ∨ x = y := by
            first
            | (have i₁ := b5e621
               have i₂ := b5e82 x y
               grind)
            | exact superpose b5e82 b5e621
            | (have j1 := b5e82 x y
               grind)
            | (have r₁ := b5e621
               have r₂ := b5e82 (σ (M.op y y)) (σ (k y x))
               grind)
            | (have r₁ := b5e621
               have r₂ := b5e82 (σ (k y x)) (σ (M.op y y))
               grind)
            | exact resolve b5e621 b5e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e82
          have b5e674 : (σ (M.op y y)) ≠ (σ (M.op y x)) ∨ y = (k y x) := by
            first
            | (have r₁ := b5e672
               have r₂ := b5e21
               grind)
            | exact resolve b5e672 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e672
          have b5e675 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b5e674
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e674
            | exact resolve b5e674 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e674
          have b5e676 : y = (k y x) := by grind
          clear b5e675
          have b5e1789 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
            intro X0
            first
            | (have i₁ := b5e608 X0
               have i₂ := b5e676
               grind)
            | exact superpose b5e676 b5e608
            | exact resolve b5e608 b5e676
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e608 b5e676
          have b5e2017 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (k x y))) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e1789 X0
               have i₂ := b5e83 x y
               grind)
            | exact superpose b5e83 b5e1789
            | (have j1 := b5e83 x y
               grind)
            | exact resolve b5e1789 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83 b5e1789
          have b5e2086 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (k x y))) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            intro X0
            first
            | (have j0 := b5e2017 X0
               grind)
            | (have r₁ := b5e2017 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e2017 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2017
          have b5e2096 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b5e2086 X0
               have i₂ := b5e63
               grind)
            | exact superpose b5e63 b5e2086
            | exact resolve b5e2086 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63 b5e2086
          have b5e2101 : ∀ X0 : G, (σ (M.op y y)) = (σ (k y x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e2096 X0
               have i₂ := b5e581
               grind)
            | exact superpose b5e581 b5e2096
            | (have j0 := b5e2096 X0
               grind)
            | exact resolve b5e2096 b5e581
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e581 b5e2096
          have b5e2102 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b5e2101 X0
               grind)
            | (have r₁ := b5e2101 X0
               have r₂ := b5e621
               grind)
            | exact resolve b5e2101 b5e621
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e621 b5e2101
          have b5e2195 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e2102 (σ y)
               grind)
            | exact superpose b5e2102 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e2102 (σ y)
               grind)
            | exact resolve b5e24 b5e2102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2102
          have b5e2198 : False := by grind
          exact b5e2198
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : (M.op y x) ≠ (M.op y y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e40 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 X1 (M.op X0 X1)
               have i₂ := b7e13 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e59 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e61 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e17 X1 (σ X0)
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e17
            | (have j0 := b7e17 (σ X0) X1
               grind)
            | exact resolve b7e17 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e63 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e59
          have b7e64 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e23
               grind)
            | exact resolve b7e63 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e65 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e64
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e64
            | exact resolve b7e64 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e69 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e14
            | exact resolve b7e14 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
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
          have b7e83 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (M.op X0 (M.op X0 X1))) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 X0 X0
               have i₂ := b7e18 X1 X0
               grind)
            | (have i₁ := b7e13 X0 X1 X0
               have i₂ := b7e18 X0 X1
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X1 X0
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e99 : x = (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
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
          have b7e100 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e99
               have r₂ := b7e22
               grind)
            | exact resolve b7e99 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99
          have b7e102 : x = (M.op x y) := by
            first
            | (have r₁ := b7e100
               have r₂ := b7e21
               grind)
            | exact resolve b7e100 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e100
          have b7e108 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) := by
            intro X0
            first
            | (have i₁ := b7e40 (σ y) (σ x) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e40
            | exact resolve b7e40 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e121 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e108 X0
               have i₂ := b7e40 (σ y) (σ y) X0
               grind)
            | exact superpose b7e40 b7e108
            | exact resolve b7e108 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e108
          have b7e126 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b7e40 x y X0
               have i₂ := b7e102
               grind)
            | exact superpose b7e102 b7e40
            | exact resolve b7e40 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e127 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x y
               have i₂ := b7e102
               grind)
            | exact superpose b7e102 b7e13
            | exact resolve b7e13 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e226 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e30 x
               have i₂ := b7e121 (σ x)
               grind)
            | exact superpose b7e121 b7e30
            | exact resolve b7e30 b7e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e121
          have b7e340 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op X0 x) ∨ (M.op y x) = (k y x) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b7e83 x y X0
               have i₂ := b7e102
               grind)
            | exact superpose b7e102 b7e83
            | (have j0 := b7e83 x y x
               grind)
            | exact resolve b7e83 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83 b7e102
          have b7e372 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op X0 x) ∨ (M.op y x) = (k y x) := by
            intro X0
            first
            | (have j0 := b7e340 X0
               grind)
            | (have r₁ := b7e340 X0
               have r₂ := b7e21
               grind)
            | exact resolve b7e340 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e340
          have b7e377 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op y x) = (k y x) := by
            intro X0
            first
            | (have i₁ := b7e372 X0
               have i₂ := b7e126 X0
               grind)
            | exact superpose b7e126 b7e372
            | exact resolve b7e372 b7e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e126 b7e372
          have b7e6598 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e61 x (σ y)
               have i₂ := b7e226
               grind)
            | exact superpose b7e226 b7e61
            | (have j0 := b7e61 x (σ y)
               grind)
            | (have r₁ := b7e61 x (σ y)
               have r₂ := b7e226
               grind)
            | exact resolve b7e61 b7e226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61 b7e226
          have b7e6640 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
          clear b7e6598
          have b7e6647 : (σ y) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b7e6640
               have r₂ := b7e23
               grind)
            | exact resolve b7e6640 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6640
          have b7e6663 : (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e6647
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e6647
            | exact resolve b7e6647 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6647
          have b7e6680 : (k y x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e6663
               grind)
            | exact superpose b7e6663 b7e14
            | exact resolve b7e14 b7e6663
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6663
          have b7e6715 : y = (k y x) := by
            first
            | (have i₁ := b7e6680
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e6680
            | exact resolve b7e6680 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6680
          have b7e7601 : ∀ X0 : G, y = (M.op y x) ∨ (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e377 X0
               have i₂ := b7e6715
               grind)
            | exact superpose b7e6715 b7e377
            | (have j0 := b7e377 X0
               grind)
            | exact resolve b7e377 b7e6715
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e377 b7e6715
          have b7e9784 : (M.op y y) ≠ (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e7601 y
               grind)
            | exact superpose b7e7601 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e7601 y
               grind)
            | exact resolve b7e22 b7e7601
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7601
          have b7e9792 : y = (M.op y x) := by grind
          clear b7e9784
          have b7e9998 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e127 X0
               have i₂ := b7e9792
               grind)
            | exact superpose b7e9792 b7e127
            | exact resolve b7e127 b7e9792
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e127 b7e9792
          have b7e10845 : (M.op y y) ≠ (M.op y y) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e9998 y
               grind)
            | exact superpose b7e9998 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e9998 y
               grind)
            | exact resolve b7e22 b7e9998
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9998
          have b7e10854 : False := by grind
          exact b7e10854
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : (M.op y x) ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e86 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e86
            | (have j0 := b8e86 X0 X1
               grind)
            | exact resolve b8e86 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e86
          have b8e475 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e90 x y
               grind)
            | exact superpose b8e90 b8e20
            | (have j1 := b8e90 x y
               grind)
            | exact resolve b8e20 b8e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90
          have b8e540 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e475
               have r₂ := b8e23
               grind)
            | exact resolve b8e475 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e475
          have b8e5836 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e540
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e540
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e540
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e540
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e540 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e540
          have b8e5837 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by grind
          clear b8e5836
          have b8e5842 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ x = y := by
            first
            | (have r₁ := b8e5837
               have r₂ := b8e22
               grind)
            | exact resolve b8e5837 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5837
          have b8e5847 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e5842
               have r₂ := b8e21
               grind)
            | exact resolve b8e5842 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5842
          have b8e5852 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e5847
               grind)
            | exact superpose b8e5847 b8e24
            | exact resolve b8e24 b8e5847
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5847
          have b8e5908 : False := by grind
          exact b8e5908

/-- `Equation3350`: `x ◇ y = y ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation3350 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3350 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3350.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e33 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (σ y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X0 (M.op X1 X1)))) := by
        intro X0 X1
        grind
      have b0e38 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e37 X0 X1
           have i₂ := b0e11 X0 X0 X1
           grind)
        | exact superpose b0e11 b0e37
        | exact resolve b0e37 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e40 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 y
           have i₂ := b0e33 y X0
           grind)
        | exact superpose b0e33 b0e11
        | exact resolve b0e11 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 y) (M.op X0 (M.op X0 y))) := by
        intro X0
        grind
      have b0e43 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 y) (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e42 X0
           have i₂ := b0e33 X0 X0
           grind)
        | exact superpose b0e33 b0e42
        | exact resolve b0e42 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e47 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 (M.op X0 (M.op X1 X1))) ∨ (M.op X2 X2) = (M.op X0 (M.op X1 X1)) ∨ (k X2 (M.op X0 (M.op X1 X1))) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X2 (M.op X0 (M.op X1 X1))
           have i₂ := b0e11 X0 (M.op X0 (M.op X1 X1)) X1
           grind)
        | exact superpose b0e11 b0e15
        | (have j0 := b0e15 X2 (M.op X0 (M.op X1 X1))
           grind)
        | exact resolve b0e15 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e50 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X2 X2) = (M.op X0 (M.op X1 X1)) ∨ (k X2 (M.op X0 (M.op X1 X1))) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e47 X0 X1 X2
           have i₂ := b0e11 X0 X0 X1
           grind)
        | exact superpose b0e11 b0e47
        | (have j0 := b0e47 X0 X1 X2
           grind)
        | (have r₁ := b0e47 (M.op X2 X2) X2 X2
           have r₂ := b0e11 (M.op X2 X2) (M.op X2 X2) X2
           grind)
        | exact resolve b0e47 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e53 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e40 (M.op y X0) X1
           have i₂ := b0e40 X0 y
           grind)
        | exact superpose b0e40 b0e40
        | exact resolve b0e40 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e56 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 y X1 X0
           have i₂ := b0e40 (M.op X0 X0) X1
           grind)
        | exact superpose b0e40 b0e11
        | exact resolve b0e11 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e53 X0 X1
           have i₂ := b0e33 X0 X1
           grind)
        | exact superpose b0e33 b0e53
        | exact resolve b0e53 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e53
      have b0e83 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 X2))) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X1 (M.op X2 X2))) = (k (M.op X1 (M.op X2 X2)) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 (M.op X1 (M.op X2 X2)) X2
           have i₂ := b0e16 (M.op X1 (M.op X2 X2)) X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X1 (M.op X0 (M.op X2 X2)))
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e95 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
      have b0e105 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X1 (M.op X2 X2))) = (k (M.op X1 (M.op X2 X2)) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e83 X0 X1 X2
           have i₂ := b0e11 X1 X1 X2
           grind)
        | exact superpose b0e11 b0e83
        | (have j0 := b0e83 X0 X1 X2
           grind)
        | exact resolve b0e83 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83
      have b0e119 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (M.op X1 (M.op X2 X2)) X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e105 X0 X1 X2
           have i₂ := b0e11 X1 X0 X2
           grind)
        | exact superpose b0e11 b0e105
        | (have j0 := b0e105 X0 X1 X2
           grind)
        | exact resolve b0e105 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e105
      have b0e146 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e40 X0 (M.op X1 X1)
           have i₂ := b0e56 X1 (M.op y X0)
           grind)
        | exact superpose b0e56 b0e40
        | exact resolve b0e40 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e149 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e146 X0 X1
           have i₂ := b0e40 X0 y
           grind)
        | exact superpose b0e40 b0e146
        | exact resolve b0e146 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e146
      have b0e416 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op X0 (M.op y X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e40 X1 (M.op y X0)
           have i₂ := b0e63 X0 (M.op y X1)
           grind)
        | exact superpose b0e63 b0e40
        | exact resolve b0e40 b0e63
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63
      have b0e425 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e416 X0 X1
           have i₂ := b0e40 X1 X0
           grind)
        | exact superpose b0e40 b0e416
        | exact resolve b0e416 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e416
      have b0e655 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e40 y X0
           have i₂ := b0e149 X0 y
           grind)
        | exact superpose b0e149 b0e40
        | exact resolve b0e40 b0e149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1185 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e40 X0 X1
           have i₂ := b0e425 X0 X1
           grind)
        | exact superpose b0e425 b0e40
        | exact resolve b0e40 b0e425
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e1188 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 y X0 X1
           have i₂ := b0e425 (M.op X1 X1) X0
           grind)
        | exact superpose b0e425 b0e11
        | exact resolve b0e11 b0e425
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1189 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e34 y X0
           have i₂ := b0e425 (σ y) X0
           grind)
        | exact superpose b0e425 b0e34
        | exact resolve b0e34 b0e425
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34 b0e425
      have b0e1707 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e1189 (σ x)
           grind)
        | exact superpose b0e1189 b0e18
        | exact resolve b0e18 b0e1189
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1189
      have b0e2275 : ∀ X0 X1 X2 : G, (k X0 X0) = X0 ∨ (M.op (M.op X1 X1) X0) = (k (M.op (M.op X1 X1) (M.op X2 X2)) X0) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e38 (M.op X1 X1) X1
           have i₂ := b0e119 X0 (M.op X1 X1) X2
           grind)
        | (have i₁ := b0e38 X0 X1
           have i₂ := b0e119 (M.op X0 (M.op X1 X1)) X1 X2
           grind)
        | exact superpose b0e119 b0e38
        | (have j1 := b0e119 X0 (M.op X1 X1) X2
           grind)
        | exact resolve b0e38 b0e119
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e2366 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op (M.op X1 X1) y) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e2275 X0 X1 x
           have i₂ := b0e149 (M.op X1 X1) x
           grind)
        | exact superpose b0e149 b0e2275
        | (have j0 := b0e2275 X0 X1 x
           grind)
        | exact resolve b0e2275 b0e149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2275
      have b0e2491 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op y (M.op X1 X1)) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e2366 X0 X1
           have i₂ := b0e655 (M.op X1 X1)
           grind)
        | exact superpose b0e655 b0e2366
        | (have j0 := b0e2366 X0 X1
           grind)
        | exact resolve b0e2366 b0e655
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2366
      have b0e2563 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op y y) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e2491 X0 X1
           have i₂ := b0e149 y X1
           grind)
        | exact superpose b0e149 b0e2491
        | (have j0 := b0e2491 X0 X1
           grind)
        | exact resolve b0e2491 b0e149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2491
      have b0e2614 : ∀ X0 : G, (M.op y X0) = (k (M.op y y) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e2563 X0 x
           have i₂ := b0e56 x X0
           grind)
        | exact superpose b0e56 b0e2563
        | (have j0 := b0e2563 X0 x
           grind)
        | exact resolve b0e2563 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2563
      have b0e4948 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e95 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e95
      have b0e4949 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e4948 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4948
      have b0e5243 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (M.op X2 X2) = X0 ∨ (k X2 X0) = X2 ∨ (M.op (M.op X1 X1) X0) = (k (M.op (M.op X1 X1) (M.op X3 X3)) X0) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e50 (M.op X1 X1) X1 X2
           have i₂ := b0e119 X0 (M.op X1 X1) X2
           grind)
        | (have i₁ := b0e50 X0 X1 X2
           have i₂ := b0e119 (M.op X0 (M.op X1 X1)) X1 X2
           grind)
        | exact superpose b0e119 b0e50
        | (have j1 := b0e119 X0 (M.op X1 X1) X3
           grind)
        | (have r₁ := b0e50 X1 X1 X2
           have r₂ := b0e119 (M.op X1 (M.op X1 X1)) X1 X2
           grind)
        | (have r₁ := b0e50 (M.op X1 X1) X1 X2
           have r₂ := b0e119 (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1) X2
           grind)
        | exact resolve b0e50 b0e119
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50 b0e119
      have b0e5255 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = X0 ∨ (k X2 X0) = X2 ∨ (M.op (M.op X1 X1) X0) = (k (M.op (M.op X1 X1) (M.op X3 X3)) X0) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e5243 X0 X1 X2 X3
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5243
      have b0e5282 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = X0 ∨ (k X2 X0) = X2 ∨ (M.op (M.op X1 X1) X0) = (k (M.op (M.op X1 X1) (M.op X3 X3)) X0) := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e5255 X0 X1 X2 X3
           have j1 := b0e15 X2 X0
           grind)
        | (have r₁ := b0e5255 X1 X1 X1 X3
           have r₂ := b0e15 X0 X1
           grind)
        | (have r₁ := b0e5255 (M.op (M.op X2 X2) (M.op X2 X2)) X1 X2 X3
           have r₂ := b0e15 X0 (M.op X2 X2)
           grind)
        | (have r₁ := b0e5255 X1 X1 X2 X3
           have r₂ := b0e15 X0 X1
           grind)
        | exact resolve b0e5255 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5255
      have b0e5358 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (k (M.op (M.op X1 X1) y) X0) ∨ (M.op X2 X2) = X0 ∨ (k X2 X0) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e5282 X0 X1 X2 x
           have i₂ := b0e149 (M.op X1 X1) x
           grind)
        | exact superpose b0e149 b0e5282
        | (have j0 := b0e5282 X0 X1 X2 x
           grind)
        | exact resolve b0e5282 b0e149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5282
      have b0e5425 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (k (M.op y (M.op X1 X1)) X0) ∨ (M.op X2 X2) = X0 ∨ (k X2 X0) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e5358 X0 X1 X2
           have i₂ := b0e655 (M.op X1 X1)
           grind)
        | exact superpose b0e655 b0e5358
        | (have j0 := b0e5358 X0 X1 X2
           grind)
        | exact resolve b0e5358 b0e655
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e655 b0e5358
      have b0e5489 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (k (M.op y y) X0) ∨ (M.op X2 X2) = X0 ∨ (k X2 X0) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e5425 X0 X1 X2
           have i₂ := b0e149 y X1
           grind)
        | exact superpose b0e149 b0e5425
        | (have j0 := b0e5425 X0 X1 X2
           grind)
        | exact resolve b0e5425 b0e149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e149 b0e5425
      have b0e5533 : ∀ X0 X2 : G, (M.op y X0) = (k (M.op y y) X0) ∨ (M.op X2 X2) = X0 ∨ (k X2 X0) = X2 := by
        intro X0 X2
        first
        | (have i₁ := b0e5489 X0 x X2
           have i₂ := b0e56 x X0
           grind)
        | exact superpose b0e56 b0e5489
        | (have j0 := b0e5489 X0 x X2
           grind)
        | exact resolve b0e5489 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5489
      have b0e11094 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
        first
        | (have i₁ := b0e4949 (M.op y y)
           have i₂ := b0e43 y
           grind)
        | exact superpose b0e43 b0e4949
        | (have j0 := b0e4949 (M.op y y)
           grind)
        | exact resolve b0e4949 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e4949
      have b0e11106 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
      clear b0e11094
      have b0e15849 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op y X0) = (k (M.op y y) X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e16 X0 X0
           have i₂ := b0e2614 X0
           grind)
        | exact superpose b0e2614 b0e16
        | (have j0 := b0e16 X0 X0
           have j1 := b0e2614 X0
           grind)
        | exact resolve b0e16 b0e2614
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2614
      have b0e15887 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op y X0) = (k (M.op y y) X0) := by
        intro X0
        first
        | (have j0 := b0e15849 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15849
      have b0e17162 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op y X0) = (k (M.op y y) X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      clear b0e5533
      have b0e17310 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op y X0) = (k (M.op y y) X0) := by
        intro X0 X1
        first
        | (have j0 := b0e17162 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e17162
      have b0e44874 : ∀ X0 : G, (M.op y X0) = (M.op (σ (M.op y y)) X0) := by
        intro X0
        first
        | (have i₁ := b0e56 (σ (M.op y y)) X0
           have i₂ := b0e11106
           grind)
        | exact superpose b0e11106 b0e56
        | exact resolve b0e56 b0e11106
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56
      have b0e44916 : ∀ X0 : G, (M.op y X0) = (M.op X0 (σ (M.op y y))) := by
        intro X0
        first
        | (have i₁ := b0e1188 X0 (σ (M.op y y))
           have i₂ := b0e11106
           grind)
        | exact superpose b0e11106 b0e1188
        | exact resolve b0e1188 b0e11106
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46201 : (σ (M.op y y)) = (M.op y (σ (M.op y y))) := by
        first
        | (have i₁ := b0e11106
           have i₂ := b0e44874 (σ (M.op y y))
           grind)
        | exact superpose b0e44874 b0e11106
        | exact resolve b0e11106 b0e44874
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e11106 b0e44874
      have b0e46501 : (M.op y y) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e46201
           have i₂ := b0e44916 y
           grind)
        | exact superpose b0e44916 b0e46201
        | exact resolve b0e46201 b0e44916
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44916 b0e46201
      have b0e47980 : ∀ X0 : G, (k (M.op y y) (σ X0)) = (σ (k (M.op y y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 (M.op y y) X0
           have i₂ := b0e46501
           grind)
        | exact superpose b0e46501 b0e17
        | exact resolve b0e17 b0e46501
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46501
      have b0e63448 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y X1) ∨ (M.op y X0) = (k (M.op y y) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e1188 X1 X0
           have i₂ := b0e15887 X0
           grind)
        | exact superpose b0e15887 b0e1188
        | (have j1 := b0e15887 X0
           grind)
        | exact resolve b0e1188 b0e15887
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1188 b0e15887
      have b0e67737 : ∀ X0 : G, (M.op y X0) ≠ (M.op y y) ∨ (M.op y X0) = (k (M.op y y) X0) := by
        intro X0
        first
        | (have j0 := b0e17310 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e17310
      have b0e67744 : ∀ X0 : G, (M.op y X0) = (k (M.op y y) X0) := by
        intro X0
        first
        | (have j0 := b0e67737 X0
           have j1 := b0e63448 X0 x
           grind)
        | (have r₁ := b0e67737 X0
           have r₂ := b0e63448 X0 y
           grind)
        | (have r₁ := b0e67737 y
           have r₂ := b0e63448 y y
           grind)
        | exact resolve b0e67737 b0e63448
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63448 b0e67737
      have b0e68680 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k (M.op y y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e47980 X0
           have i₂ := b0e67744 (σ X0)
           grind)
        | exact superpose b0e67744 b0e47980
        | exact resolve b0e47980 b0e67744
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47980
      have b0e68793 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e68680 X0
           have i₂ := b0e67744 X0
           grind)
        | exact superpose b0e67744 b0e68680
        | exact resolve b0e68680 b0e67744
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67744 b0e68680
      have b0e73637 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op y (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e68793 X0
           have i₂ := b0e1185 y X0
           grind)
        | (have i₁ := b0e68793 X0
           have i₂ := b0e1185 X0 y
           grind)
        | exact superpose b0e1185 b0e68793
        | exact resolve b0e68793 b0e1185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1185 b0e68793
      have b0e74989 : (M.op y (σ x)) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b0e1707
           have i₂ := b0e73637 x
           grind)
        | exact superpose b0e73637 b0e1707
        | (have r₁ := b0e1707
           have r₂ := b0e73637 x
           grind)
        | exact resolve b0e1707 b0e73637
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1707 b0e73637
      have b0e75021 : False := by grind
      exact b0e75021
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
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
        have b1e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b1e35 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (σ y))) := by
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
        have b1e42 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 y
             have i₂ := b1e35 y X0
             grind)
          | exact superpose b1e35 b1e12
          | exact resolve b1e12 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e59 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 y X1 X0
             have i₂ := b1e42 (M.op X0 X0) X1
             grind)
          | exact superpose b1e42 b1e12
          | exact resolve b1e12 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e99 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e17 (σ X1) (σ X0)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X1) (σ X0)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e101 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
        have b1e104 : y = (M.op y y) := by grind
        clear b1e101
        have b1e155 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e28 X1 X0
             grind)
          | exact superpose b1e28 b1e13
          | exact resolve b1e13 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e164 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e59 (σ y) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e59
          | exact resolve b1e59 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e205 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e36 (σ y) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e36
          | exact resolve b1e36 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e232 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e205 X0
             have i₂ := b1e164 X0
             grind)
          | exact superpose b1e164 b1e205
          | exact resolve b1e205 b1e164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e164 b1e205
        have b1e386 : (σ y) = (M.op y (σ y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e232 (σ y)
             grind)
          | exact superpose b1e232 b1e22
          | exact resolve b1e22 b1e232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e389 : (σ y) = (M.op y y) := by
          first
          | (have i₁ := b1e386
             have i₂ := b1e232 y
             grind)
          | exact superpose b1e232 b1e386
          | exact resolve b1e386 b1e232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e232 b1e386
        have b1e403 : y = (σ y) := by
          first
          | (have i₁ := b1e389
             have i₂ := b1e104
             grind)
          | exact superpose b1e104 b1e389
          | exact resolve b1e389 b1e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e104 b1e389
        have b1e5139 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e99 x x
             grind)
          | exact superpose b1e99 b1e21
          | (have j1 := b1e99 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e99 y x
             grind)
          | exact resolve b1e21 b1e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e99
        have b1e5289 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e5139
        have b1e5335 : y ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e5289
             have i₂ := b1e403
             grind)
          | exact superpose b1e403 b1e5289
          | exact resolve b1e5289 b1e403
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5289
        have b1e7360 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b1e155
        have b1e7377 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e7360 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e7360
          | exact resolve b1e7360 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7360
        have b1e11598 : y ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e5335
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e5335
          | (have j1 := b1e17 (σ x) (σ x)
             grind)
          | exact resolve b1e5335 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5335
        have b1e11606 : y ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e11598
        have b1e11613 : y ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e11606
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e11606
          | exact resolve b1e11606 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11606
        have b1e11620 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b1e11613
             have r₂ := b1e403
             grind)
          | exact resolve b1e11613 b1e403
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e403 b1e11613
        have b1e11627 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e11620
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e11620
          | exact resolve b1e11620 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11620
        have b1e12367 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b1e7377 x
             have i₂ := b1e11627
             grind)
          | exact superpose b1e11627 b1e7377
          | exact resolve b1e7377 b1e11627
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7377 b1e11627
        have b1e12408 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b1e12367
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e12367
          | exact resolve b1e12367 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12367
        have b1e12613 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e12408
             grind)
          | exact superpose b1e12408 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e12408
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12408
        have b1e12622 : x = (M.op x x) ∨ x = y := by grind
        clear b1e12613
        have b1e12637 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e12622
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12622
          | exact resolve b1e12622 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12622
        have b1e12638 : x = y := by grind
        clear b1e12637
        have b1e12769 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e12638
             grind)
          | exact superpose b1e12638 b1e21
          | exact resolve b1e21 b1e12638
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12638
        have b1e12779 : False := by grind
        exact b1e12779
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e18
          | exact resolve b2e18 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e76 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
        have b2e88 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
        have b2e210 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e26 X1 X0
             grind)
          | exact superpose b2e26 b2e13
          | exact resolve b2e13 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e1054 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e76 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76
        have b2e1055 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e1054
             have r₂ := b2e22
             grind)
          | exact resolve b2e1054 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1054
        have b2e1056 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1055
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1055
          | exact resolve b2e1055 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1055
        have b2e1057 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e1056
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1056
          | exact resolve b2e1056 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1056
        have b2e3555 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e210
        have b2e3569 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e3555 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e3555
          | exact resolve b2e3555 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3555
        have b2e4217 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e88 x x
             grind)
          | exact superpose b2e88 b2e21
          | (have j1 := b2e88 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e88 y x
             grind)
          | exact resolve b2e21 b2e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e88
        have b2e4360 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e4217
        have b2e10455 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e4360
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e4360
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e4360 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4360
        have b2e10463 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e10455
        have b2e10473 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e10463
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e10463
          | exact resolve b2e10463 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10463
        have b2e10474 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e10473
        have b2e10484 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e10474
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e10474
          | exact resolve b2e10474 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10474
        have b2e10498 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e3569 x
             have i₂ := b2e10484
             grind)
          | exact superpose b2e10484 b2e3569
          | exact resolve b2e3569 b2e10484
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3569 b2e10484
        have b2e10535 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e10498
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e10498
          | exact resolve b2e10498 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10498
        have b2e10802 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e10535
             grind)
          | exact superpose b2e10535 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e10535
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10535
        have b2e10811 : x = (M.op x x) ∨ x = y := by grind
        clear b2e10802
        have b2e10831 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e10811
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e10811
          | exact resolve b2e10811 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10811
        have b2e10832 : x = y := by grind
        clear b2e10831
        have b2e11116 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e1057
             have i₂ := b2e10832
             grind)
          | exact superpose b2e10832 b2e1057
          | exact resolve b2e1057 b2e10832
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1057 b2e10832
        have b2e11121 : False := by grind
        exact b2e11121
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e35 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 y)) := by
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
        have b3e42 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e35 y X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e35
          | exact resolve b3e35 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 y
             have i₂ := b3e35 y X0
             grind)
          | exact superpose b3e35 b3e12
          | exact resolve b3e12 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 X0
             have i₂ := b3e17 (σ X1) (σ X0)
             grind)
          | exact superpose b3e17 b3e18
          | (have j1 := b3e17 (σ X1) (σ X0)
             grind)
          | exact resolve b3e18 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e110 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 y X1 X0
             have i₂ := b3e43 (M.op X0 X0) X1
             grind)
          | exact superpose b3e43 b3e12
          | exact resolve b3e12 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e141 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e110 (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e110
          | exact resolve b3e110 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e157 : ∀ X0 : G, (M.op y y) = (M.op y (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e42 (M.op X0 X0)
             have i₂ := b3e110 X0 y
             grind)
          | exact superpose b3e110 b3e42
          | exact resolve b3e42 b3e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e110
        have b3e160 : ∀ X0 : G, y = (M.op y (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e157 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e157
          | exact resolve b3e157 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e157
        have b3e192 : y = (M.op y (σ y)) := by
          first
          | (have i₁ := b3e160 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e160
          | exact resolve b3e160 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e160
        have b3e4313 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e82 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e82
          | exact resolve b3e82 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e82
        have b3e4531 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e4313
        have b3e10945 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e4531
             grind)
          | exact superpose b3e4531 b3e13
          | exact resolve b3e13 b3e4531
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e10965 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e10945
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e10945
          | exact resolve b3e10945 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10945
        have b3e12419 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e10965
             grind)
          | exact superpose b3e10965 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e10965
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10965
        have b3e12427 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b3e12419
        have b3e12435 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e12427
             have r₂ := b3e20
             grind)
          | exact resolve b3e12427 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12427
        have b3e12562 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e12435
        have b3e12831 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e4531
             have i₂ := b3e12562
             grind)
          | exact superpose b3e12562 b3e4531
          | exact resolve b3e4531 b3e12562
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4531 b3e12562
        have b3e12842 : (σ x) = (σ y) := by grind
        clear b3e12831
        have b3e12957 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e12842
             grind)
          | exact superpose b3e12842 b3e19
          | exact resolve b3e19 b3e12842
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e12958 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e12842
             grind)
          | exact superpose b3e12842 b3e22
          | exact resolve b3e22 b3e12842
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e12962 : x = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e12842
             grind)
          | exact superpose b3e12842 b3e13
          | exact resolve b3e13 b3e12842
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12842
        have b3e12998 : x = y := by
          first
          | (have i₁ := b3e12962
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e12962
          | exact resolve b3e12962 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12962
        have b3e13000 : (σ y) = (M.op y (σ y)) := by
          first
          | (have i₁ := b3e12958
             have i₂ := b3e141 (σ y)
             grind)
          | exact superpose b3e141 b3e12958
          | exact resolve b3e12958 b3e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12958
        have b3e13001 : (σ (M.op x y)) ≠ (M.op y (σ y)) := by
          first
          | (have i₁ := b3e12957
             have i₂ := b3e141 (σ y)
             grind)
          | exact superpose b3e141 b3e12957
          | exact resolve b3e12957 b3e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e141 b3e12957
        have b3e13011 : y = (σ y) := by
          first
          | (have i₁ := b3e13000
             have i₂ := b3e192
             grind)
          | exact superpose b3e192 b3e13000
          | exact resolve b3e13000 b3e192
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13000
        have b3e13012 : y ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b3e13001
             have i₂ := b3e192
             grind)
          | exact superpose b3e192 b3e13001
          | exact resolve b3e13001 b3e192
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e192 b3e13001
        have b3e13021 : y ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b3e13012
             have i₂ := b3e42 x
             grind)
          | exact superpose b3e42 b3e13012
          | exact resolve b3e13012 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42 b3e13012
        have b3e13023 : y ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e13021
             have i₂ := b3e12998
             grind)
          | exact superpose b3e12998 b3e13021
          | exact resolve b3e13021 b3e12998
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12998 b3e13021
        have b3e13025 : y ≠ (σ y) := by
          first
          | (have i₁ := b3e13023
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e13023
          | exact resolve b3e13023 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13023
        have b3e13026 : False := by grind
        exact b3e13026
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e37 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 y)) := by
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
          have b4e38 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (σ y))) := by
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
          have b4e41 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X0 (M.op X1 X1)))) := by
            intro X0 X1
            grind
          have b4e42 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e41 X0 X1
               have i₂ := b4e13 X0 X0 X1
               grind)
            | exact superpose b4e13 b4e41
            | exact resolve b4e41 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e44 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e37 y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e37
            | exact resolve b4e37 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 y
               have i₂ := b4e37 y X0
               grind)
            | exact superpose b4e37 b4e13
            | exact resolve b4e13 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e73 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 X2))) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X1 (M.op X2 X2))) = (k (M.op X1 (M.op X2 X2)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 (M.op X1 (M.op X2 X2)) X2
               have i₂ := b4e18 (M.op X1 (M.op X2 X2)) X0
               grind)
            | (have i₁ := b4e13 X0 X1 X2
               have i₂ := b4e18 X0 (M.op X1 (M.op X0 (M.op X2 X2)))
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X0 X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e93 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X1 (M.op X2 X2))) = (k (M.op X1 (M.op X2 X2)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e73 X0 X1 X2
               have i₂ := b4e13 X1 X1 X2
               grind)
            | exact superpose b4e13 b4e73
            | (have j0 := b4e73 X0 X1 X2
               grind)
            | exact resolve b4e73 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e99 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (M.op X1 (M.op X2 X2)) X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e93 X0 X1 X2
               have i₂ := b4e13 X1 X0 X2
               grind)
            | exact superpose b4e13 b4e93
            | (have j0 := b4e93 X0 X1 X2
               grind)
            | exact resolve b4e93 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93
          have b4e111 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 y X1 X0
               have i₂ := b4e45 (M.op X0 X0) X1
               grind)
            | exact superpose b4e45 b4e13
            | exact resolve b4e13 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e144 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e111 (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e111
            | exact resolve b4e111 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e159 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e45 X0 (M.op X1 X1)
               have i₂ := b4e111 X1 (M.op y X0)
               grind)
            | exact superpose b4e111 b4e45
            | exact resolve b4e45 b4e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e160 : ∀ X0 : G, (M.op y y) = (M.op y (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e44 (M.op X0 X0)
               have i₂ := b4e111 X0 y
               grind)
            | exact superpose b4e111 b4e44
            | exact resolve b4e44 b4e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e163 : ∀ X0 : G, y = (M.op y (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e160 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e160
            | exact resolve b4e160 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e160
          have b4e164 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e159 X0 X1
               have i₂ := b4e45 X0 y
               grind)
            | exact superpose b4e45 b4e159
            | exact resolve b4e159 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45 b4e159
          have b4e183 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e38 (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e38
            | exact resolve b4e38 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e210 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e183 X0
               have i₂ := b4e144 X0
               grind)
            | exact superpose b4e144 b4e183
            | exact resolve b4e183 b4e144
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e144 b4e183
          have b4e526 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e210 (σ x)
               grind)
            | exact superpose b4e210 b4e20
            | exact resolve b4e20 b4e210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e527 : (σ y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b4e24
               have i₂ := b4e210 (σ y)
               grind)
            | exact superpose b4e210 b4e24
            | exact resolve b4e24 b4e210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e530 : (σ y) = (M.op y y) := by
            first
            | (have i₁ := b4e527
               have i₂ := b4e210 y
               grind)
            | exact superpose b4e210 b4e527
            | exact resolve b4e527 b4e210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e210 b4e527
          have b4e531 : (M.op y (σ x)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b4e526
               have i₂ := b4e44 x
               grind)
            | exact superpose b4e44 b4e526
            | exact resolve b4e526 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e526
          have b4e546 : y = (σ y) := by
            first
            | (have i₁ := b4e530
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e530
            | exact resolve b4e530 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e530
          have b4e660 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 y X0
               have i₂ := b4e546
               grind)
            | exact superpose b4e546 b4e19
            | exact resolve b4e19 b4e546
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1921 : ∀ X0 X1 X2 : G, (k X0 X0) = X0 ∨ (M.op (M.op X1 X1) X0) = (k (M.op (M.op X1 X1) (M.op X2 X2)) X0) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e42 (M.op X1 X1) X1
               have i₂ := b4e99 X0 (M.op X1 X1) X2
               grind)
            | (have i₁ := b4e42 X0 X1
               have i₂ := b4e99 (M.op X0 (M.op X1 X1)) X1 X2
               grind)
            | exact superpose b4e99 b4e42
            | (have j1 := b4e99 X0 (M.op X1 X1) X2
               grind)
            | exact resolve b4e42 b4e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e1935 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X0) = (k (M.op X2 (M.op X3 X3)) X0) ∨ (M.op X2 X2) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e17 X1 X0
               have i₂ := b4e99 X0 X2 X3
               grind)
            | exact superpose b4e99 b4e17
            | (have j0 := b4e17 X1 X0
               have j1 := b4e99 X0 X2 X3
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e99 X0 X0 X2
               grind)
            | (have r₁ := b4e17 X0 (M.op X1 X1)
               have r₂ := b4e99 (M.op (M.op X1 X1) (M.op X1 X1)) X1 X2
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e99 X0 X1 X2
               grind)
            | exact resolve b4e17 b4e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1961 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X0) = (k (M.op X2 (M.op X3 X3)) X0) ∨ (M.op X2 X2) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b4e1935 X0 X1 X2 X3
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1935
          have b4e1991 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k (M.op X2 y) X0) ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e1961 X0 X1 X2 x
               have i₂ := b4e164 X2 x
               grind)
            | exact superpose b4e164 b4e1961
            | (have j0 := b4e1961 X0 X1 X1 x
               grind)
            | exact resolve b4e1961 b4e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1961
          have b4e2005 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op (M.op X1 X1) y) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e1921 X0 X1 x
               have i₂ := b4e164 (M.op X1 X1) x
               grind)
            | exact superpose b4e164 b4e1921
            | (have j0 := b4e1921 X0 X1 x
               grind)
            | exact resolve b4e1921 b4e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1921
          have b4e2112 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op y (M.op X1 X1)) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e2005 X0 X1
               have i₂ := b4e44 (M.op X1 X1)
               grind)
            | exact superpose b4e44 b4e2005
            | (have j0 := b4e2005 X0 X1
               grind)
            | exact resolve b4e2005 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e2005
          have b4e2172 : ∀ X0 X1 : G, (k y X0) = (M.op (M.op X1 X1) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e2112 X0 X1
               have i₂ := b4e163 X1
               grind)
            | exact superpose b4e163 b4e2112
            | (have j0 := b4e2112 X0 X1
               grind)
            | exact resolve b4e2112 b4e163
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2112
          have b4e2215 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e2172 X0 x
               have i₂ := b4e111 x X0
               grind)
            | exact superpose b4e111 b4e2172
            | (have j0 := b4e2172 X0 x
               grind)
            | exact resolve b4e2172 b4e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2172
          have b4e2278 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 y) ∨ (M.op X2 X0) = (k (M.op X2 (M.op X3 X3)) X0) ∨ (M.op X2 X2) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e164 X1 X0
               have i₂ := b4e99 X0 X2 X3
               grind)
            | exact superpose b4e99 b4e164
            | (have j1 := b4e99 X0 X2 X3
               grind)
            | exact resolve b4e164 b4e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99
          have b4e2407 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k (M.op X2 y) X0) ∨ (M.op X1 X0) = (M.op X1 y) ∨ (M.op X2 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e2278 X0 X1 X2 x
               have i₂ := b4e164 X2 x
               grind)
            | exact superpose b4e164 b4e2278
            | (have j0 := b4e2278 X0 X1 X2 x
               grind)
            | exact resolve b4e2278 b4e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e164 b4e2278
          have b4e14908 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op y X0) = (k y X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e18 X0 X0
               have i₂ := b4e2215 X0
               grind)
            | exact superpose b4e2215 b4e18
            | (have j0 := b4e18 X0 X0
               have j1 := b4e2215 X0
               grind)
            | exact resolve b4e18 b4e2215
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2215
          have b4e14941 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op y X0) = (k y X0) := by
            intro X0
            first
            | (have j0 := b4e14908 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14908
          have b4e15093 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y X1) ∨ (M.op y X0) = (k y X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e111 X0 X1
               have i₂ := b4e14941 X0
               grind)
            | exact superpose b4e14941 b4e111
            | (have j1 := b4e14941 X0
               grind)
            | exact resolve b4e111 b4e14941
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e111
          have b4e15097 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e163 X0
               have i₂ := b4e14941 X0
               grind)
            | exact superpose b4e14941 b4e163
            | (have j1 := b4e14941 X0
               grind)
            | exact resolve b4e163 b4e14941
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e163 b4e14941
          have b4e76960 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 y) ∨ (M.op X0 X1) = (k (M.op X0 y) X1) ∨ (M.op (M.op X0 y) (M.op X0 y)) = X1 ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e1991 X1 (M.op X0 y) X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1991
          have b4e77015 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 y) X1) ∨ (M.op (M.op X0 y) (M.op X0 y)) = X1 ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e76960 X0 X1
               have j1 := b4e2407 X1 X1 X0
               grind)
            | (have r₁ := b4e76960 X1 X0
               have r₂ := b4e2407 X0 X1 x
               grind)
            | (have r₁ := b4e76960 X1 y
               have r₂ := b4e2407 y X1 x
               grind)
            | (have r₁ := b4e76960 x x
               have r₂ := b4e2407 (M.op x y) X1 x
               grind)
            | exact resolve b4e76960 b4e2407
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2407 b4e76960
          have b4e77036 : ∀ X0 X1 : G, (M.op X0 (M.op X0 y)) = X1 ∨ (M.op X0 X1) = (k (M.op X0 y) X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e77015 X0 X1
               have i₂ := b4e37 X0 (M.op X0 y)
               grind)
            | exact superpose b4e37 b4e77015
            | (have j0 := b4e77015 X0 X1
               grind)
            | exact resolve b4e77015 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77015
          have b4e77049 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k (M.op X0 y) X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e77036 X0 X1
               have i₂ := b4e37 X0 X0
               grind)
            | exact superpose b4e37 b4e77036
            | (have j0 := b4e77036 X0 X1
               grind)
            | exact resolve b4e77036 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e77036
          have b4e77050 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k (M.op X0 y) X1) := by
            intro X0 X1
            first
            | (have j0 := b4e77049 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77049
          have b4e81189 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b4e77050 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e77050
            | exact resolve b4e77050 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77050
          have b4e82196 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) ∨ (τ X0) = y := by
            intro X0
            first
            | (have i₁ := b4e30 X0 y
               have i₂ := b4e81189 (τ X0)
               grind)
            | exact superpose b4e81189 b4e30
            | (have j1 := b4e81189 (τ X0)
               grind)
            | exact resolve b4e30 b4e81189
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e81189
          have b4e82212 : ∀ X0 : G, (k y X0) = (σ (M.op y (τ X0))) ∨ (τ X0) = y := by
            intro X0
            first
            | (have i₁ := b4e82196 X0
               have i₂ := b4e546
               grind)
            | exact superpose b4e546 b4e82196
            | (have j0 := b4e82196 X0
               grind)
            | exact resolve b4e82196 b4e546
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e82196
          have b4e85334 : ∀ X0 : G, (k y (σ X0)) = (σ (M.op y X0)) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b4e82212 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e82212
            | exact resolve b4e82212 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e82212
          have b4e85401 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b4e85334 X0
               have i₂ := b4e660 X0
               grind)
            | exact superpose b4e660 b4e85334
            | (have j0 := b4e85334 X0
               grind)
            | exact resolve b4e85334 b4e660
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85334
          have b4e91369 : (σ y) ≠ (M.op y (σ x)) ∨ (M.op y (σ x)) = (k y (σ x)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e15093 (σ x) (σ x)
               grind)
            | exact superpose b4e15093 b4e23
            | (have j1 := b4e15093 (σ x) x
               grind)
            | exact resolve b4e23 b4e15093
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15093
          have b4e91539 : y ≠ (M.op y (σ x)) ∨ (M.op y (σ x)) = (k y (σ x)) := by
            first
            | (have i₁ := b4e91369
               have i₂ := b4e546
               grind)
            | exact superpose b4e546 b4e91369
            | exact resolve b4e91369 b4e546
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e546 b4e91369
          have b4e91638 : (M.op y (σ x)) = (k y (σ x)) := by
            first
            | (have j1 := b4e15097 (σ x)
               grind)
            | (have r₁ := b4e91539
               have r₂ := b4e15097 (σ x)
               grind)
            | exact resolve b4e91539 b4e15097
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15097 b4e91539
          have b4e91650 : (M.op y (σ x)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e91638
               have i₂ := b4e660 x
               grind)
            | exact superpose b4e660 b4e91638
            | exact resolve b4e91638 b4e660
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e660 b4e91638
          have b4e92911 : (M.op y (σ x)) = (σ (M.op y x)) ∨ x = y := by
            first
            | (have i₁ := b4e85401 x
               have i₂ := b4e91650
               grind)
            | exact superpose b4e91650 b4e85401
            | (have j0 := b4e85401 x
               grind)
            | exact resolve b4e85401 b4e91650
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85401 b4e91650
          have b4e92939 : x = y := by
            first
            | (have r₁ := b4e92911
               have r₂ := b4e531
               grind)
            | exact resolve b4e92911 b4e531
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e531 b4e92911
          have b4e93759 : (σ y) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e92939
               grind)
            | exact superpose b4e92939 b4e23
            | exact resolve b4e23 b4e92939
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92939
          have b4e93773 : False := by grind
          exact b4e93773
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : y = (k y y) := by grind
          have b5e79 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
          have b5e4019 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e79 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79
          have b5e4020 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e4019 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4019
          have b5e11482 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e4020 y
               have i₂ := b5e26
               grind)
            | exact superpose b5e26 b5e4020
            | (have j0 := b5e4020 y
               grind)
            | exact resolve b5e4020 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e4020
          have b5e11486 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e11482
          have b5e11504 : False := by grind
          exact b5e11504
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b6e40 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e42 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X1 X2 (M.op X0 X0)
             have i₂ := b6e12 (M.op X0 X0) X1 X0
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e57 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (σ y) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 (σ y)
             have i₂ := b6e40 (σ y) X0
             grind)
          | exact superpose b6e40 b6e12
          | exact resolve b6e12 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e17 (σ X1) (σ X0)
             grind)
          | exact superpose b6e17 b6e18
          | (have j1 := b6e17 (σ X1) (σ X0)
             grind)
          | exact resolve b6e18 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e95 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
        have b6e97 : (σ x) = (σ (M.op y x)) ∨ y = (M.op y y) := by
          first
          | (have r₁ := b6e95
             have r₂ := b6e20
             grind)
          | exact resolve b6e95 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95
        have b6e108 : (σ x) = (σ (M.op y x)) := by
          first
          | (have r₁ := b6e97
             have r₂ := b6e21
             grind)
          | exact resolve b6e97 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e97
        have b6e122 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 (σ y)) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e42 X1 (M.op X0 (σ y)) X2
             have i₂ := b6e40 X0 (M.op X1 X1)
             grind)
          | exact superpose b6e40 b6e42
          | exact resolve b6e42 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e132 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op X1 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e40 (M.op X1 X1) X0
             have i₂ := b6e42 X1 (σ y) X0
             grind)
          | exact superpose b6e42 b6e40
          | exact resolve b6e40 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e148 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op (M.op X0 (σ y)) X2) := by
          intro X0 X2
          first
          | (have i₁ := b6e122 X0 x X2
             have i₂ := b6e12 X0 X2 x
             grind)
          | exact superpose b6e12 b6e122
          | exact resolve b6e122 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e122
        have b6e554 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ y) (M.op (σ y) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e57 X0 (M.op X1 X1)
             have i₂ := b6e132 (M.op (σ y) X0) X1
             grind)
          | exact superpose b6e132 b6e57
          | exact resolve b6e57 b6e132
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e132
        have b6e557 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e554 X0 X1
             have i₂ := b6e57 X0 (σ y)
             grind)
          | exact superpose b6e57 b6e554
          | exact resolve b6e554 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e554
        have b6e691 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (σ y))) = (M.op X0 (M.op (σ y) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e57 X1 (M.op X0 (σ y))
             have i₂ := b6e148 X0 (M.op (σ y) X1)
             grind)
          | exact superpose b6e148 b6e57
          | exact resolve b6e57 b6e148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e148
        have b6e694 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b6e691 X0 X1
             have i₂ := b6e57 X1 X0
             grind)
          | exact superpose b6e57 b6e691
          | exact resolve b6e691 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e691
        have b6e1942 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b6e57 (σ y) X0
             have i₂ := b6e557 X0 (σ y)
             grind)
          | exact superpose b6e557 b6e57
          | exact resolve b6e57 b6e557
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57 b6e557
        have b6e2069 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e1942 (σ x)
             grind)
          | exact superpose b6e1942 b6e19
          | exact resolve b6e19 b6e1942
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1942
        have b6e2917 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e40 X0 X1
             have i₂ := b6e694 X0 X1
             grind)
          | exact superpose b6e694 b6e40
          | exact resolve b6e40 b6e694
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e694
        have b6e3093 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
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
        have b6e3294 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e3093
        have b6e9390 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e3294
             grind)
          | exact superpose b6e3294 b6e13
          | exact resolve b6e13 b6e3294
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e9407 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e9390
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e9390
          | exact resolve b6e9390 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9390
        have b6e9419 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e9407
             grind)
          | exact superpose b6e9407 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e9407
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9407
        have b6e9427 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e9419
        have b6e9435 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e9427
             have r₂ := b6e20
             grind)
          | exact resolve b6e9427 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9427
        have b6e9637 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e9435
        have b6e9923 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3294
             have i₂ := b6e9637
             grind)
          | exact superpose b6e9637 b6e3294
          | exact resolve b6e3294 b6e9637
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3294 b6e9637
        have b6e9934 : (σ x) = (σ y) := by grind
        clear b6e9923
        have b6e10030 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e9934
             grind)
          | exact superpose b6e9934 b6e22
          | exact resolve b6e22 b6e9934
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e10033 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e2069
             have i₂ := b6e9934
             grind)
          | exact superpose b6e9934 b6e2069
          | exact resolve b6e2069 b6e9934
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2069
        have b6e10058 : (M.op (σ y) (σ y)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b6e10033
             have i₂ := b6e2917 x y
             grind)
          | (have i₁ := b6e10033
             have i₂ := b6e2917 y x
             grind)
          | exact superpose b6e2917 b6e10033
          | exact resolve b6e10033 b6e2917
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2917 b6e10033
        have b6e10060 : (σ x) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e10058
             have i₂ := b6e108
             grind)
          | exact superpose b6e108 b6e10058
          | exact resolve b6e10058 b6e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e108 b6e10058
        have b6e10062 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e10060
             have i₂ := b6e10030
             grind)
          | exact superpose b6e10030 b6e10060
          | exact resolve b6e10060 b6e10030
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e10030 b6e10060
        have b6e10064 : False := by grind
        exact b6e10064
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b7e84 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
          have b7e87 : y = (M.op y y) := by grind
          clear b7e84
          have b7e91 : False := by grind
          exact b7e91
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
            intro X0 X1 X2
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b8e29 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X2 (M.op X0 X0)
               have i₂ := b8e13 (M.op X0 X0) X1 X0
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e60 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
          have b8e94 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op (M.op X2 X2) X0) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e29 X1 (M.op (M.op X2 X2) X0) X3
               have i₂ := b8e29 X2 X0 (M.op X1 X1)
               grind)
            | exact superpose b8e29 b8e29
            | exact resolve b8e29 b8e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e114 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X2 X2) X0) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b8e94 X0 x X2 X3
               have i₂ := b8e13 X0 X3 x
               grind)
            | exact superpose b8e13 b8e94
            | exact resolve b8e94 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e94
          have b8e462 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e60 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e463 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b8e462
               have r₂ := b8e24
               grind)
            | exact resolve b8e462 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e462
          have b8e464 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e463
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e463
            | exact resolve b8e463 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e463
          have b8e512 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = (M.op X2 (M.op (M.op X3 X3) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e29 X3 X0 (M.op (M.op X1 X1) X2)
               have i₂ := b8e114 X2 X1 (M.op (M.op X3 X3) X0)
               grind)
            | exact superpose b8e114 b8e29
            | exact resolve b8e29 b8e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e114
          have b8e513 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e512 X0 X1 X2 x
               have i₂ := b8e29 x X0 X2
               grind)
            | exact superpose b8e29 b8e512
            | exact resolve b8e512 b8e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e512
          have b8e1164 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e29 x X0 X1
               have i₂ := b8e513 X1 x X0
               grind)
            | exact superpose b8e513 b8e29
            | exact resolve b8e29 b8e513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29 b8e513
          have b8e1564 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1164 (σ x) (σ y)
               grind)
            | (have i₁ := b8e20
               have i₂ := b8e1164 (σ y) (σ x)
               grind)
            | exact superpose b8e1164 b8e20
            | exact resolve b8e20 b8e1164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1565 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e1564
               have i₂ := b8e464
               grind)
            | exact superpose b8e464 b8e1564
            | exact resolve b8e1564 b8e464
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e464 b8e1564
          have b8e1567 : (σ (k x y)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b8e1565
               have i₂ := b8e1164 x y
               grind)
            | (have i₁ := b8e1565
               have i₂ := b8e1164 y x
               grind)
            | exact superpose b8e1164 b8e1565
            | exact resolve b8e1565 b8e1164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1164 b8e1565
          have b8e1805 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e1567
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1567
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1567 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1567
          have b8e1813 : y = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e1805
          have b8e1818 : y = (M.op y y) := by
            first
            | (have r₁ := b8e1813
               have r₂ := b8e21
               grind)
            | exact resolve b8e1813 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1813
          have b8e1819 : False := by grind
          exact b8e1819

/-- `Equation3364`: `x ◇ y = y ◇ (z ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pyx_Equation3364 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3364 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3364.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
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
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
      have b0e79 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e29
      have b0e83 : False := by grind
      exact b0e83
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 (M.op X0 X2))) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
          have b4e33 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b4e13 x X0 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X2 (M.op X0 X1)
               have i₂ := b4e13 X0 (M.op X0 X1) X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e58 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e69 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e58 X0 X1
               have i₂ := b4e31 X1
               grind)
            | exact superpose b4e31 b4e58
            | (have j0 := b4e58 X0 X1
               grind)
            | exact resolve b4e58 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e58
          have b4e114 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X0 X2)) X3) = (M.op X3 (M.op X1 (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e36 X1 (M.op X2 (M.op X0 X2)) X3
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e36
            | exact resolve b4e36 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e115 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X1 (M.op X0 X1))) = (M.op (M.op X2 (M.op X2 X0)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e36 X1 (M.op X2 (M.op X2 X0)) X3
               have i₂ := b4e36 X2 X0 X1
               grind)
            | exact superpose b4e36 b4e36
            | exact resolve b4e36 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e116 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op X1 (M.op X0 (M.op x X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e36 X0 (M.op x y) X1
               have i₂ := b4e33 X0
               grind)
            | exact superpose b4e33 b4e36
            | exact resolve b4e36 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e118 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e36 X1 (M.op X0 X1) X2
               have i₂ := b4e13 X0 X1 X1
               grind)
            | exact superpose b4e13 b4e36
            | exact resolve b4e36 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e119 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e36 X1 (M.op X1 X0) X2
               have i₂ := b4e36 X1 X0 X1
               grind)
            | exact superpose b4e36 b4e36
            | exact resolve b4e36 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e130 : ∀ X1 : G, (M.op x X1) = (M.op (M.op x y) X1) := by
            intro X1
            first
            | (have i₁ := b4e116 x X1
               have i₂ := b4e13 x X1 x
               grind)
            | exact superpose b4e13 b4e116
            | exact resolve b4e116 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e116
          have b4e131 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X2 (M.op X2 X0)) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e115 X0 x X2 X3
               have i₂ := b4e13 X0 X3 x
               grind)
            | exact superpose b4e13 b4e115
            | exact resolve b4e115 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115
          have b4e132 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X2 (M.op X0 X2)) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e114 X0 x X2 X3
               have i₂ := b4e13 X0 X3 x
               grind)
            | exact superpose b4e13 b4e114
            | exact resolve b4e114 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e114
          have b4e170 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op X1 X0))) = (M.op X1 (M.op x y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op x y) X0
               have i₂ := b4e130 (M.op X0 (M.op X1 X0))
               grind)
            | exact superpose b4e130 b4e13
            | exact resolve b4e13 b4e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e171 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op x (M.op X0 (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e36 X0 X1 (M.op x y)
               have i₂ := b4e130 (M.op X0 (M.op X0 X1))
               grind)
            | exact superpose b4e130 b4e36
            | exact resolve b4e36 b4e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130
          have b4e175 : ∀ X1 : G, (M.op X1 (M.op x y)) = (M.op X1 x) := by
            intro X1
            first
            | (have i₁ := b4e171 x X1
               have i₂ := b4e36 x X1 x
               grind)
            | exact superpose b4e36 b4e171
            | exact resolve b4e171 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e171
          have b4e176 : ∀ X0 X1 : G, (M.op x X1) = (M.op x (M.op X0 (M.op X1 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e170 X0 X1
               have i₂ := b4e33 X1
               grind)
            | exact superpose b4e33 b4e170
            | exact resolve b4e170 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e170
          have b4e187 : ∀ X1 : G, (M.op x X1) = (M.op X1 x) := by
            intro X1
            first
            | (have i₁ := b4e176 x X1
               have i₂ := b4e13 X1 x x
               grind)
            | exact superpose b4e13 b4e176
            | exact resolve b4e176 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e176
          have b4e534 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e69 x y
               grind)
            | exact superpose b4e69 b4e20
            | (have j1 := b4e69 x y
               grind)
            | exact resolve b4e20 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e572 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have r₁ := b4e534
               have r₂ := b4e23
               grind)
            | exact resolve b4e534 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e534
          have b4e1088 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op x y) X0) := by
            intro X0
            first
            | (have i₁ := b4e175 X0
               have i₂ := b4e118 x y X0
               grind)
            | (have i₁ := b4e175 (M.op X0 x)
               have i₂ := b4e118 X0 x (M.op x y)
               grind)
            | exact superpose b4e118 b4e175
            | exact resolve b4e175 b4e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e175
          have b4e1319 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e118 X0 X1 X2
               have i₂ := b4e119 X0 X1 X2
               grind)
            | (have i₁ := b4e118 X0 X1 (M.op X1 X0)
               have i₂ := b4e119 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b4e119 b4e118
            | exact resolve b4e118 b4e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e118 b4e119
          have b4e1513 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X2 (M.op X3 (M.op X3 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e36 X3 X0 (M.op X1 (M.op X1 X2))
               have i₂ := b4e131 X2 X1 (M.op X3 (M.op X3 X0))
               grind)
            | exact superpose b4e131 b4e36
            | exact resolve b4e36 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e131
          have b4e1530 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e1513 X0 X1 X2 x
               have i₂ := b4e36 x X0 X2
               grind)
            | exact superpose b4e36 b4e1513
            | exact resolve b4e1513 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1513
          have b4e2858 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op X1 (M.op X3 (M.op X3 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e132 X1 X0 (M.op X3 (M.op X3 X2))
               have i₂ := b4e1530 (M.op X0 (M.op X1 X0)) X3 X2
               grind)
            | exact superpose b4e1530 b4e132
            | exact resolve b4e132 b4e1530
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132 b4e1530
          have b4e2861 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e2858 X0 X1 X2 x
               have i₂ := b4e36 x X2 X1
               grind)
            | exact superpose b4e36 b4e2858
            | exact resolve b4e2858 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e2858
          have b4e6353 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b4e572
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e572
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e572
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e572
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e572 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e6355 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y := by grind
          clear b4e6353
          have b4e6359 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b4e6355
               have r₂ := b4e21
               grind)
            | exact resolve b4e6355 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6355
          have b4e6366 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e14 (M.op y y)
               have i₂ := b4e6359
               grind)
            | exact superpose b4e6359 b4e14
            | exact resolve b4e14 b4e6359
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6359
          have b4e6397 : x = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e6366
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e6366
            | exact resolve b4e6366 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6366
          have b4e6398 : x = (M.op y y) := by grind
          clear b4e6397
          have b4e6428 : y = (k y x) ∨ x = y := by grind
          have b4e6450 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op y x) X0) := by
            intro X0
            first
            | (have i₁ := b4e2861 y y X0
               have i₂ := b4e6398
               grind)
            | exact superpose b4e6398 b4e2861
            | exact resolve b4e2861 b4e6398
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2861 b4e6398
          have b4e6451 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x y) X0) := by
            intro X0
            first
            | (have i₁ := b4e6450 X0
               have i₂ := b4e1319 y x X0
               grind)
            | (have i₁ := b4e6450 X0
               have i₂ := b4e1319 x y X0
               grind)
            | exact superpose b4e1319 b4e6450
            | exact resolve b4e6450 b4e1319
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1319 b4e6450
          have b4e6467 : y = (k y x) := by
            first
            | (have r₁ := b4e6428
               have r₂ := b4e21
               grind)
            | exact resolve b4e6428 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6428
          have b4e6468 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e6451 X0
               have i₂ := b4e1088 X0
               grind)
            | exact superpose b4e1088 b4e6451
            | exact resolve b4e6451 b4e1088
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1088 b4e6451
          have b4e6661 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e572
               have i₂ := b4e6467
               grind)
            | exact superpose b4e6467 b4e572
            | exact resolve b4e572 b4e6467
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e572 b4e6467
          have b4e6667 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e6661
               have i₂ := b4e6468 x
               grind)
            | exact superpose b4e6468 b4e6661
            | exact resolve b4e6661 b4e6468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6661
          have b4e6672 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e6667
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e6667
            | exact resolve b4e6667 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6667
          have b4e6673 : (σ x) = (σ (M.op y y)) := by grind
          clear b4e6672
          have b4e6676 : (σ x) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e6673
               have i₂ := b4e6468 y
               grind)
            | exact superpose b4e6468 b4e6673
            | exact resolve b4e6673 b4e6468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6673
          have b4e6677 : (σ (M.op x y)) = (σ x) := by
            first
            | (have i₁ := b4e6676
               have i₂ := b4e187 y
               grind)
            | exact superpose b4e187 b4e6676
            | exact resolve b4e6676 b4e187
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e187 b4e6676
          have b4e6678 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e6677
               have i₂ := b4e6468 x
               grind)
            | exact superpose b4e6468 b4e6677
            | exact resolve b4e6677 b4e6468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6468 b4e6677
          have b4e6679 : (σ x) = (σ y) := by
            first
            | (have i₁ := b4e6678
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e6678
            | exact resolve b4e6678 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6678
          have b4e6680 : False := by grind
          exact b4e6680
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b5e100 : (σ y) ≠ (σ (M.op x x)) := by
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
          have b5e105 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e100
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e100
            | exact resolve b5e100 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e100
          have b5e106 : False := by grind
          exact b5e106
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
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b7e104 : (σ y) = (σ (M.op x x)) := by
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
          have b7e143 : (M.op x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e104
               grind)
            | exact superpose b7e104 b7e14
            | exact resolve b7e14 b7e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e104
          have b7e144 : y = (M.op x x) := by
            first
            | (have i₁ := b7e143
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e143
            | exact resolve b7e143 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e143
          have b7e148 : False := by grind
          exact b7e148
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 (M.op X0 X2))) := by
            intro X0 X1 X2
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
          have b8e34 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X2 (M.op X0 X1)
               have i₂ := b8e13 X0 (M.op X0 X1) X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = X0 := by
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
          have b8e87 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X1 (M.op X0 X1))) = (M.op (M.op X2 (M.op X2 X0)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e34 X1 (M.op X2 (M.op X2 X0)) X3
               have i₂ := b8e34 X2 X0 X1
               grind)
            | exact superpose b8e34 b8e34
            | exact resolve b8e34 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e100 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X2 (M.op X2 X0)) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b8e87 X0 x X2 X3
               have i₂ := b8e13 X0 X3 x
               grind)
            | exact superpose b8e13 b8e87
            | exact resolve b8e87 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e87
          have b8e244 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have j0 := b8e65 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e245 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b8e244
               have r₂ := b8e23
               grind)
            | exact resolve b8e244 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e244
          have b8e246 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e245
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e245
            | exact resolve b8e245 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e245
          have b8e881 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X2 (M.op X3 (M.op X3 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e34 X3 X0 (M.op X1 (M.op X1 X2))
               have i₂ := b8e100 X2 X1 (M.op X3 (M.op X3 X0))
               grind)
            | exact superpose b8e100 b8e34
            | exact resolve b8e34 b8e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e100
          have b8e903 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e881 X0 X1 X2 x
               have i₂ := b8e34 x X0 X2
               grind)
            | exact superpose b8e34 b8e881
            | exact resolve b8e881 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e881
          have b8e1599 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e34 x X0 X1
               have i₂ := b8e903 X1 x X0
               grind)
            | exact superpose b8e903 b8e34
            | exact resolve b8e34 b8e903
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34 b8e903
          have b8e1871 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e246
               have i₂ := b8e1599 (σ y) (σ x)
               grind)
            | (have i₁ := b8e246
               have i₂ := b8e1599 (σ x) (σ y)
               grind)
            | exact superpose b8e1599 b8e246
            | exact resolve b8e246 b8e1599
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e246
          have b8e1929 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1871
               grind)
            | exact superpose b8e1871 b8e20
            | exact resolve b8e20 b8e1871
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1871
          have b8e2061 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e1929
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1929
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e1929
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e1929
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e1929 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1929
          have b8e2063 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y := by
            first
            | (have r₁ := b8e2061
               have r₂ := b8e22
               grind)
            | exact resolve b8e2061 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2061
          have b8e2067 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
            first
            | (have r₁ := b8e2063
               have r₂ := b8e21
               grind)
            | exact resolve b8e2063 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2063
          have b8e2074 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e2067
               have i₂ := b8e1599 y x
               grind)
            | (have i₁ := b8e2067
               have i₂ := b8e1599 x y
               grind)
            | exact superpose b8e1599 b8e2067
            | exact resolve b8e2067 b8e1599
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1599 b8e2067
          have b8e2075 : False := by grind
          exact b8e2075

/-- `Equation3473`: `x ◇ x = y ◇ ((x ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3473 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3473.models_iff G M).mp hM
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
        have b1e55 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e59 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e55
        have b1e61 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e59
             have r₂ := b1e23
             grind)
          | exact resolve b1e59 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e62 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e61
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e61
          | exact resolve b1e61 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e63 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e62
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e62
          | exact resolve b1e62 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e62
        have b1e64 : False := by grind
        exact b1e64
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
        have b2e84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e157 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e84 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84
        have b2e3322 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e157 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e157
          | (have j0 := b2e157 x y
             grind)
          | exact resolve b2e157 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e157
        have b2e3331 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e3322
        have b2e3341 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e3331
             have r₂ := b2e22
             grind)
          | exact resolve b2e3331 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3331
        have b2e3345 : False := by grind
        exact b2e3345
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
        have b3e41 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
        have b3e43 : x = y ∨ x = (k x y) := by grind
        clear b3e41
        have b3e44 : x = (k x y) := by
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
          have b5e54 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e58 : x = y ∨ x = (k x y) := by grind
          clear b5e54
          have b5e60 : x = (k x y) := by
            first
            | (have r₁ := b5e58
               have r₂ := b5e25
               grind)
            | exact resolve b5e58 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e58
          have b5e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e170 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e63 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e3587 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e170 x y
               have i₂ := b5e60
               grind)
            | exact superpose b5e60 b5e170
            | (have j0 := b5e170 x y
               grind)
            | exact resolve b5e170 b5e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60 b5e170
          have b5e3596 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e3587
          have b5e3606 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e3596
               have r₂ := b5e24
               grind)
            | exact resolve b5e3596 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3596
          have b5e3610 : False := by grind
          exact b5e3610
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
        have b6e61 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
        have b6e63 : y = (M.op x y) ∨ x = (M.op x y) := by grind
        clear b6e61
        have b6e66 : x = (M.op x y) := by
          first
          | (have r₁ := b6e63
             have r₂ := b6e21
             grind)
          | exact resolve b6e63 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63
        have b6e69 : False := by grind
        exact b6e69
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
          have b7e50 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e54 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e50
          have b7e56 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e54
               have r₂ := b7e25
               grind)
            | exact resolve b7e54 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e54
          have b7e57 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e56
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e56
            | exact resolve b7e56 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e60 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e57
               grind)
            | exact superpose b7e57 b7e14
            | exact resolve b7e14 b7e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e61 : x = (k x y) := by
            first
            | (have i₁ := b7e60
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e60
            | exact resolve b7e60 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e70 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e61
               grind)
            | exact superpose b7e61 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e71 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b7e70
          have b7e73 : y = (M.op x y) := by
            first
            | (have r₁ := b7e71
               have r₂ := b7e21
               grind)
            | exact resolve b7e71 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e75 : False := by grind
          exact b7e75
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
          have b8e78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e147 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e78 x y
               grind)
            | exact superpose b8e78 b8e20
            | (have j1 := b8e78 x y
               grind)
            | exact resolve b8e20 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e173 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e147
               have r₂ := b8e24
               grind)
            | exact resolve b8e147 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147
          have b8e176 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e173
               have r₂ := b8e23
               grind)
            | exact resolve b8e173 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e173
          have b8e177 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e176
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e176
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e176 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e176
          have b8e178 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e177
          have b8e179 : x = (M.op x y) := by
            first
            | (have r₁ := b8e178
               have r₂ := b8e22
               grind)
            | exact resolve b8e178 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e178
          have b8e180 : False := by grind
          exact b8e180

/-- `Equation3476`: `x ◇ x = y ◇ ((x ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3476 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3476 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3476.models_iff G M).mp hM
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
        have b1e50 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e52 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e50
        have b1e53 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e52
             have r₂ := b1e23
             grind)
          | exact resolve b1e52 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e54 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e53
          | exact resolve b1e53 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e55 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e54
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e54
          | exact resolve b1e54 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e54
        have b1e56 : False := by grind
        exact b1e56
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
        have b2e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e816 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e53 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e61874 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e816 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e816
          | (have j0 := b2e816 x y
             grind)
          | exact resolve b2e816 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e816
        have b2e61891 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e61874
        have b2e61918 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e61891
             have r₂ := b2e22
             grind)
          | exact resolve b2e61891 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61891
        have b2e61955 : False := by grind
        exact b2e61955
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
          have b5e46 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          clear b5e46
          have b5e51 : x = (k x y) := by
            first
            | (have r₁ := b5e50
               have r₂ := b5e25
               grind)
            | exact resolve b5e50 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e50
          have b5e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e1111 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e54 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e60097 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1111 x y
               have i₂ := b5e51
               grind)
            | exact superpose b5e51 b5e1111
            | (have j0 := b5e1111 x y
               grind)
            | exact resolve b5e1111 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51 b5e1111
          have b5e60113 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e60097
          have b5e60143 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e60113
               have r₂ := b5e24
               grind)
            | exact resolve b5e60113 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60113
          have b5e60176 : False := by grind
          exact b5e60176
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
        have b6e69 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
        have b6e71 : y = (M.op x y) ∨ x = (M.op x y) := by grind
        clear b6e69
        have b6e74 : x = (M.op x y) := by
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
          have b7e57 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e62 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e57
          have b7e64 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e25
               grind)
            | exact resolve b7e62 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e62
          have b7e65 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e64
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e64
            | exact resolve b7e64 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e68 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e14
            | exact resolve b7e14 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e69 : x = (k x y) := by
            first
            | (have i₁ := b7e68
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e68
            | exact resolve b7e68 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e78 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e79 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b7e78
          have b7e81 : y = (M.op x y) := by
            first
            | (have r₁ := b7e79
               have r₂ := b7e21
               grind)
            | exact resolve b7e79 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79
          have b7e83 : False := by grind
          exact b7e83
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
          have b8e85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e1208 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e85 x y
               grind)
            | exact superpose b8e85 b8e20
            | (have j1 := b8e85 x y
               grind)
            | exact resolve b8e20 b8e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85
          have b8e1268 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1208
               have r₂ := b8e24
               grind)
            | exact resolve b8e1208 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1208
          have b8e1272 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1268
               have r₂ := b8e23
               grind)
            | exact resolve b8e1268 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1268
          have b8e1274 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1272
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1272
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1272 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1272
          have b8e1275 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e1274
          have b8e1276 : x = (M.op x y) := by
            first
            | (have r₁ := b8e1275
               have r₂ := b8e22
               grind)
            | exact resolve b8e1275 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1275
          have b8e1277 : False := by grind
          exact b8e1277

/-- `Equation3479`: `x ◇ x = y ◇ ((x ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3479 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3479 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3479.models_iff G M).mp hM
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
        have b1e56 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e60 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e56
        have b1e61 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e60
             have r₂ := b1e23
             grind)
          | exact resolve b1e60 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e62 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e61
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e61
          | exact resolve b1e61 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e63 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e62
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e62
          | exact resolve b1e62 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e62
        have b1e64 : False := by grind
        exact b1e64
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
        have b2e77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e1390 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e77 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77
        have b2e7367 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1390 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e1390
          | (have j0 := b2e1390 x y
             grind)
          | exact resolve b2e1390 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e1390
        have b2e7374 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e7367
        have b2e7387 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e7374
             have r₂ := b2e22
             grind)
          | exact resolve b2e7374 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7374
        have b2e7399 : False := by grind
        exact b2e7399
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
          have b5e70 : x = (k x y) := by
            first
            | (have r₁ := b5e68
               have r₂ := b5e25
               grind)
            | exact resolve b5e68 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e68
          have b5e73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e825 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e73 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e23055 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e825 x y
               have i₂ := b5e70
               grind)
            | exact superpose b5e70 b5e825
            | (have j0 := b5e825 x y
               grind)
            | exact resolve b5e825 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70 b5e825
          have b5e23066 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e23055
          have b5e23078 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e23066
               have r₂ := b5e24
               grind)
            | exact resolve b5e23066 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23066
          have b5e23082 : False := by grind
          exact b5e23082
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
        have b6e72 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
        have b6e74 : y = (M.op x y) ∨ x = (M.op x y) := by grind
        clear b6e72
        have b6e77 : x = (M.op x y) := by
          first
          | (have r₁ := b6e74
             have r₂ := b6e21
             grind)
          | exact resolve b6e74 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e80 : False := by grind
        exact b6e80
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
          have b7e66 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e25
               grind)
            | exact resolve b7e64 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e64
          have b7e67 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e66
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e66
            | exact resolve b7e66 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e70 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e14
            | exact resolve b7e14 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e71 : x = (k x y) := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e70
            | exact resolve b7e70 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e80 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e81 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b7e80
          have b7e83 : y = (M.op x y) := by
            first
            | (have r₁ := b7e81
               have r₂ := b7e21
               grind)
            | exact resolve b7e81 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e85 : False := by grind
          exact b7e85
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
          have b8e89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e782 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e89 x y
               grind)
            | exact superpose b8e89 b8e20
            | (have j1 := b8e89 x y
               grind)
            | exact resolve b8e20 b8e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89
          have b8e831 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e782
               have r₂ := b8e24
               grind)
            | exact resolve b8e782 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e782
          have b8e834 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e831
               have r₂ := b8e23
               grind)
            | exact resolve b8e831 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e831
          have b8e835 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e834
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e834
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e834 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e834
          have b8e836 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e835
          have b8e837 : x = (M.op x y) := by
            first
            | (have r₁ := b8e836
               have r₂ := b8e22
               grind)
            | exact resolve b8e836 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e836
          have b8e838 : False := by grind
          exact b8e838
