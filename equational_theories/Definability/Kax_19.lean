import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4417`: `x ◇ (x ◇ y) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pxy_Equation4417 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4417 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4417.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e69 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e74 : False := by grind
      exact b0e74
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X2) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e32 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) X3) = (M.op X1 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e13 X1 (M.op X1 x) X3
               have i₂ := b4e13 X1 x X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ y) (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e13 X1 x X3
               have i₂ := b4e13 X1 x X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 : G, (M.op y y) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 y X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e39 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e39
            | exact resolve b4e39 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e43 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b4e34 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e34
            | exact resolve b4e34 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e48 : ∀ X1 : G, y = (M.op (M.op X1 y) X1) := by
            intro X1
            first
            | (have i₁ := b4e13 y x X1
               have i₂ := b4e41 x
               grind)
            | exact superpose b4e41 b4e13
            | exact resolve b4e13 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e62 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 y)) X1) = (M.op (M.op X0 y) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X0 y) X0 X1
               have i₂ := b4e48 X0
               grind)
            | exact superpose b4e48 b4e13
            | exact resolve b4e13 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e77 : (σ y) = (M.op y (M.op (σ y) y)) := by
            first
            | (have i₁ := b4e43 (M.op (σ y) y)
               have i₂ := b4e48 (σ y)
               grind)
            | exact superpose b4e48 b4e43
            | exact resolve b4e43 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e85 : y = (M.op y (σ y)) := by
            first
            | (have i₁ := b4e41 (M.op (σ y) y)
               have i₂ := b4e77
               grind)
            | exact superpose b4e77 b4e41
            | exact resolve b4e41 b4e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77
          have b4e99 : (σ y) = (M.op y y) := by
            first
            | (have i₁ := b4e43 y
               have i₂ := b4e85
               grind)
            | exact superpose b4e85 b4e43
            | exact resolve b4e43 b4e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43 b4e85
          have b4e102 : y = (σ y) := by
            first
            | (have i₁ := b4e99
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e99
            | exact resolve b4e99 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99
          have b4e118 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e102
               grind)
            | exact superpose b4e102 b4e20
            | exact resolve b4e20 b4e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e204 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X2 (M.op X1 X3)) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e35 X2 (M.op X1 X3) X1
               have i₂ := b4e13 X1 X3 X0
               grind)
            | exact superpose b4e13 b4e35
            | exact resolve b4e35 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e209 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y (M.op X1 y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e35 X0 X1 (M.op X1 y)
               have i₂ := b4e48 X1
               grind)
            | exact superpose b4e48 b4e35
            | exact resolve b4e35 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e252 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op y (M.op (M.op X1 X3) y)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e204 X0 X1 x X3
               have i₂ := b4e209 x (M.op X1 X3)
               grind)
            | exact superpose b4e209 b4e204
            | exact resolve b4e204 b4e209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e204
          have b4e273 : ∀ X1 X3 : G, (M.op y (M.op (M.op X1 X3) y)) = (M.op (M.op y (M.op X1 y)) X1) := by
            intro X1 X3
            first
            | (have i₁ := b4e252 x X1 X3
               have i₂ := b4e209 x X1
               grind)
            | exact superpose b4e209 b4e252
            | exact resolve b4e252 b4e209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e252
          have b4e451 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) X0) = (M.op (M.op y X1) (M.op y y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 y (M.op y X1) X0
               have i₂ := b4e41 X1
               grind)
            | exact superpose b4e41 b4e32
            | exact resolve b4e32 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e476 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X2 (M.op (M.op X3 X1) X3)) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e35 X2 (M.op (M.op X3 X1) X3) X1
               have i₂ := b4e32 X3 X1 X0
               grind)
            | exact superpose b4e32 b4e35
            | exact resolve b4e35 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e485 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op y (M.op (M.op (M.op X3 X1) X3) y)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e476 X0 X1 x X3
               have i₂ := b4e209 x (M.op (M.op X3 X1) X3)
               grind)
            | exact superpose b4e209 b4e476
            | exact resolve b4e476 b4e209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e476
          have b4e502 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) X0) = (M.op (M.op y X1) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e451 X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e451
            | exact resolve b4e451 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e451
          have b4e532 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op y (M.op (M.op y (M.op X1 y)) y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e485 X0 X1 x
               have i₂ := b4e209 x X1
               grind)
            | exact superpose b4e209 b4e485
            | exact resolve b4e485 b4e209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e485
          have b4e543 : ∀ X0 X1 : G, (M.op y (M.op X1 y)) = (M.op (M.op X0 (M.op y X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e502 X0 X1
               have i₂ := b4e209 y X1
               grind)
            | exact superpose b4e209 b4e502
            | exact resolve b4e502 b4e209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e502
          have b4e567 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op y (M.op y y)) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e532 X0 X1
               have i₂ := b4e273 y (M.op X1 y)
               grind)
            | exact superpose b4e273 b4e532
            | exact resolve b4e532 b4e273
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e273 b4e532
          have b4e578 : ∀ X1 : G, (M.op y (M.op X1 y)) = (M.op y (M.op (M.op y X1) y)) := by
            intro X1
            first
            | (have i₁ := b4e543 x X1
               have i₂ := b4e209 x (M.op y X1)
               grind)
            | exact superpose b4e209 b4e543
            | exact resolve b4e543 b4e209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e543
          have b4e590 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op y y) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e567 X0 X1
               have i₂ := b4e62 y y
               grind)
            | exact superpose b4e62 b4e567
            | exact resolve b4e567 b4e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62 b4e567
          have b4e594 : ∀ X1 : G, (M.op y (M.op X1 y)) = (M.op y (M.op y (M.op X1 y))) := by
            intro X1
            first
            | (have i₁ := b4e578 X1
               have i₂ := b4e209 y X1
               grind)
            | exact superpose b4e209 b4e578
            | exact resolve b4e578 b4e209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e578
          have b4e599 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X1) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e590 X0 X1
               have i₂ := b4e48 y
               grind)
            | exact superpose b4e48 b4e590
            | exact resolve b4e590 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48 b4e590
          have b4e602 : ∀ X1 : G, y = (M.op y (M.op X1 y)) := by
            intro X1
            first
            | (have i₁ := b4e594 X1
               have i₂ := b4e41 (M.op X1 y)
               grind)
            | exact superpose b4e41 b4e594
            | exact resolve b4e594 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e594
          have b4e605 : ∀ X1 : G, y = (M.op (M.op y (M.op X1 y)) X1) := by
            intro X1
            first
            | (have i₁ := b4e599 x X1
               have i₂ := b4e209 x X1
               grind)
            | exact superpose b4e209 b4e599
            | exact resolve b4e599 b4e209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e209 b4e599
          have b4e610 : ∀ X1 : G, y = (M.op y X1) := by
            intro X1
            first
            | (have i₁ := b4e605 X1
               have i₂ := b4e602 X1
               grind)
            | exact superpose b4e602 b4e605
            | exact resolve b4e605 b4e602
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e602 b4e605
          have b4e626 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op y y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 y X1 X0
               have i₂ := b4e610 X1
               grind)
            | exact superpose b4e610 b4e32
            | exact resolve b4e32 b4e610
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e628 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e35 X0 X1 y
               have i₂ := b4e610 X1
               grind)
            | exact superpose b4e610 b4e35
            | exact resolve b4e35 b4e610
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35 b4e610
          have b4e641 : ∀ X0 X1 : G, y = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e628 X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e628
            | exact resolve b4e628 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e628
          have b4e643 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e626 X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e626
            | exact resolve b4e626 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e626
          have b4e647 : ∀ X1 : G, y = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b4e643 x X1
               have i₂ := b4e641 x X1
               grind)
            | exact superpose b4e641 b4e643
            | exact resolve b4e643 b4e641
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e641 b4e643
          have b4e972 : y ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e118
               have i₂ := b4e647 (σ x)
               grind)
            | exact superpose b4e647 b4e118
            | exact resolve b4e118 b4e647
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e118
          have b4e977 : y ≠ (σ y) := by
            first
            | (have i₁ := b4e972
               have i₂ := b4e647 x
               grind)
            | exact superpose b4e647 b4e972
            | exact resolve b4e972 b4e647
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e647 b4e972
          have b4e990 : False := by grind
          exact b4e990
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b5e97 : (σ y) ≠ (σ (M.op y y)) := by
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
          have b5e103 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e97
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e97
            | exact resolve b5e97 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e97
          have b5e104 : False := by grind
          exact b5e104
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
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b7e85 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e24
            | exact resolve b7e24 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e94 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e85
               grind)
            | exact superpose b7e85 b7e14
            | exact resolve b7e14 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e95 : y = (M.op y y) := by
            first
            | (have i₁ := b7e94
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e94
            | exact resolve b7e94 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e99 : False := by grind
          exact b7e99
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e18 (σ X0) (σ X1)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (M.op (σ X1) (σ X1)) (σ X1)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e58 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e58
            | (have j0 := b8e58 X0 X1
               grind)
            | exact resolve b8e58 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e72 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e24
            | exact resolve b8e24 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e1097 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e66 x y
               grind)
            | exact superpose b8e66 b8e20
            | (have j1 := b8e66 (M.op y y) y
               grind)
            | exact resolve b8e20 b8e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e1146 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e1097
               have r₂ := b8e72
               grind)
            | exact resolve b8e1097 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72 b8e1097
          have b8e1157 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1146
               have r₂ := b8e23
               grind)
            | exact resolve b8e1146 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1146
          have b8e1174 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e1157
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1157
            | (have j1 := b8e18 (M.op y y) y
               grind)
            | (have r₁ := b8e1157
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e1157
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e1157 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1157
          have b8e1175 : y = (M.op y y) ∨ x = y := by grind
          clear b8e1174
          have b8e1177 : x = y := by
            first
            | (have r₁ := b8e1175
               have r₂ := b8e22
               grind)
            | exact resolve b8e1175 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1175
          have b8e1180 : False := by grind
          exact b8e1180

/-- `Equation4417`: `x ◇ (x ◇ y) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxy_pxx_pxy_Equation4417 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4417 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4417.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (x) (y) with h0a | h0a
  · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
      have b0e69 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e74 : False := by grind
      exact b0e74
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X2) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e32 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) X3) = (M.op X1 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e13 X1 (M.op X1 x) X3
               have i₂ := b4e13 X1 x X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ y) (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e13 X1 x X3
               have i₂ := b4e13 X1 x X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 : G, (M.op y y) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 y X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e39 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e39
            | exact resolve b4e39 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e43 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b4e34 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e34
            | exact resolve b4e34 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e48 : ∀ X1 : G, y = (M.op (M.op X1 y) X1) := by
            intro X1
            first
            | (have i₁ := b4e13 y x X1
               have i₂ := b4e41 x
               grind)
            | exact superpose b4e41 b4e13
            | exact resolve b4e13 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e62 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 y)) X1) = (M.op (M.op X0 y) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X0 y) X0 X1
               have i₂ := b4e48 X0
               grind)
            | exact superpose b4e48 b4e13
            | exact resolve b4e13 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e73 : (σ y) = (M.op y (M.op (σ y) y)) := by
            first
            | (have i₁ := b4e43 (M.op (σ y) y)
               have i₂ := b4e48 (σ y)
               grind)
            | exact superpose b4e48 b4e43
            | exact resolve b4e43 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e89 : y = (M.op y (σ y)) := by
            first
            | (have i₁ := b4e41 (M.op (σ y) y)
               have i₂ := b4e73
               grind)
            | exact superpose b4e73 b4e41
            | exact resolve b4e41 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e105 : (σ y) = (M.op y y) := by
            first
            | (have i₁ := b4e43 y
               have i₂ := b4e89
               grind)
            | exact superpose b4e89 b4e43
            | exact resolve b4e43 b4e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43 b4e89
          have b4e108 : y = (σ y) := by
            first
            | (have i₁ := b4e105
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e105
            | exact resolve b4e105 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e105
          have b4e127 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e108
               grind)
            | exact superpose b4e108 b4e20
            | exact resolve b4e20 b4e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e195 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X2 (M.op X1 X3)) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e35 X2 (M.op X1 X3) X1
               have i₂ := b4e13 X1 X3 X0
               grind)
            | exact superpose b4e13 b4e35
            | exact resolve b4e35 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e201 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y (M.op X1 y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e35 X0 X1 (M.op X1 y)
               have i₂ := b4e48 X1
               grind)
            | exact superpose b4e48 b4e35
            | exact resolve b4e35 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e245 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op y (M.op (M.op X1 X3) y)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e195 X0 X1 x X3
               have i₂ := b4e201 x (M.op X1 X3)
               grind)
            | exact superpose b4e201 b4e195
            | exact resolve b4e195 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e195
          have b4e267 : ∀ X1 X3 : G, (M.op y (M.op (M.op X1 X3) y)) = (M.op (M.op y (M.op X1 y)) X1) := by
            intro X1 X3
            first
            | (have i₁ := b4e245 x X1 X3
               have i₂ := b4e201 x X1
               grind)
            | exact superpose b4e201 b4e245
            | exact resolve b4e245 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e245
          have b4e508 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) X0) = (M.op (M.op y X1) (M.op y y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 y (M.op y X1) X0
               have i₂ := b4e41 X1
               grind)
            | exact superpose b4e41 b4e32
            | exact resolve b4e32 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e533 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X2 (M.op (M.op X3 X1) X3)) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e35 X2 (M.op (M.op X3 X1) X3) X1
               have i₂ := b4e32 X3 X1 X0
               grind)
            | exact superpose b4e32 b4e35
            | exact resolve b4e35 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e542 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op y (M.op (M.op (M.op X3 X1) X3) y)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e533 X0 X1 x X3
               have i₂ := b4e201 x (M.op (M.op X3 X1) X3)
               grind)
            | exact superpose b4e201 b4e533
            | exact resolve b4e533 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e533
          have b4e559 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) X0) = (M.op (M.op y X1) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e508 X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e508
            | exact resolve b4e508 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e508
          have b4e593 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op y (M.op (M.op y (M.op X1 y)) y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e542 X0 X1 x
               have i₂ := b4e201 x X1
               grind)
            | exact superpose b4e201 b4e542
            | exact resolve b4e542 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e542
          have b4e604 : ∀ X0 X1 : G, (M.op y (M.op X1 y)) = (M.op (M.op X0 (M.op y X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e559 X0 X1
               have i₂ := b4e201 y X1
               grind)
            | exact superpose b4e201 b4e559
            | exact resolve b4e559 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e559
          have b4e631 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op y (M.op y y)) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e593 X0 X1
               have i₂ := b4e267 y (M.op X1 y)
               grind)
            | exact superpose b4e267 b4e593
            | exact resolve b4e593 b4e267
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e267 b4e593
          have b4e642 : ∀ X1 : G, (M.op y (M.op X1 y)) = (M.op y (M.op (M.op y X1) y)) := by
            intro X1
            first
            | (have i₁ := b4e604 x X1
               have i₂ := b4e201 x (M.op y X1)
               grind)
            | exact superpose b4e201 b4e604
            | exact resolve b4e604 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e604
          have b4e656 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op y y) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e631 X0 X1
               have i₂ := b4e62 y y
               grind)
            | exact superpose b4e62 b4e631
            | exact resolve b4e631 b4e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62 b4e631
          have b4e660 : ∀ X1 : G, (M.op y (M.op X1 y)) = (M.op y (M.op y (M.op X1 y))) := by
            intro X1
            first
            | (have i₁ := b4e642 X1
               have i₂ := b4e201 y X1
               grind)
            | exact superpose b4e201 b4e642
            | exact resolve b4e642 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e642
          have b4e666 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X1) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e656 X0 X1
               have i₂ := b4e48 y
               grind)
            | exact superpose b4e48 b4e656
            | exact resolve b4e656 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48 b4e656
          have b4e669 : ∀ X1 : G, y = (M.op y (M.op X1 y)) := by
            intro X1
            first
            | (have i₁ := b4e660 X1
               have i₂ := b4e41 (M.op X1 y)
               grind)
            | exact superpose b4e41 b4e660
            | exact resolve b4e660 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e660
          have b4e672 : ∀ X1 : G, y = (M.op (M.op y (M.op X1 y)) X1) := by
            intro X1
            first
            | (have i₁ := b4e666 x X1
               have i₂ := b4e201 x X1
               grind)
            | exact superpose b4e201 b4e666
            | exact resolve b4e666 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e201 b4e666
          have b4e677 : ∀ X1 : G, y = (M.op y X1) := by
            intro X1
            first
            | (have i₁ := b4e672 X1
               have i₂ := b4e669 X1
               grind)
            | exact superpose b4e669 b4e672
            | exact resolve b4e672 b4e669
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e669 b4e672
          have b4e693 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op y y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 y X1 X0
               have i₂ := b4e677 X1
               grind)
            | exact superpose b4e677 b4e32
            | exact resolve b4e32 b4e677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e695 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e35 X0 X1 y
               have i₂ := b4e677 X1
               grind)
            | exact superpose b4e677 b4e35
            | exact resolve b4e35 b4e677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35 b4e677
          have b4e708 : ∀ X0 X1 : G, y = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e695 X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e695
            | exact resolve b4e695 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e695
          have b4e710 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e693 X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e693
            | exact resolve b4e693 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e693
          have b4e714 : ∀ X1 : G, y = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b4e710 x X1
               have i₂ := b4e708 x X1
               grind)
            | exact superpose b4e708 b4e710
            | exact resolve b4e710 b4e708
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e708 b4e710
          have b4e1060 : (σ y) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e127
               have i₂ := b4e714 x
               grind)
            | exact superpose b4e714 b4e127
            | exact resolve b4e127 b4e714
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e127
          have b4e1063 : y ≠ (σ y) := by
            first
            | (have i₁ := b4e1060
               have i₂ := b4e714 (σ x)
               grind)
            | exact superpose b4e714 b4e1060
            | exact resolve b4e1060 b4e714
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e714 b4e1060
          have b4e1077 : False := by grind
          exact b4e1077
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b5e91 : (σ y) ≠ (σ (M.op y y)) := by
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
          have b5e97 : (σ y) ≠ (σ y) := by
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
          have b5e98 : False := by grind
          exact b5e98
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
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e85 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e24
            | exact resolve b7e24 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e94 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e85
               grind)
            | exact superpose b7e85 b7e14
            | exact resolve b7e14 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e95 : y = (M.op y y) := by
            first
            | (have i₁ := b7e94
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e94
            | exact resolve b7e94 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e99 : False := by grind
          exact b7e99
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e18 (σ X0) (σ X1)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (M.op (σ X1) (σ X1)) (σ X1)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e58 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e58
            | (have j0 := b8e58 X0 X1
               grind)
            | exact resolve b8e58 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e72 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e24
            | exact resolve b8e24 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e1144 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e66 x y
               grind)
            | exact superpose b8e66 b8e20
            | (have j1 := b8e66 (M.op y y) y
               grind)
            | exact resolve b8e20 b8e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e1193 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e1144
               have r₂ := b8e72
               grind)
            | exact resolve b8e1144 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72 b8e1144
          have b8e1204 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1193
               have r₂ := b8e23
               grind)
            | exact resolve b8e1193 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1193
          have b8e1221 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e1204
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1204
            | (have j1 := b8e18 (M.op y y) y
               grind)
            | (have r₁ := b8e1204
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e1204
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e1204 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1204
          have b8e1222 : y = (M.op y y) ∨ x = y := by grind
          clear b8e1221
          have b8e1224 : x = y := by
            first
            | (have r₁ := b8e1222
               have r₂ := b8e22
               grind)
            | exact resolve b8e1222 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1222
          have b8e1227 : False := by grind
          exact b8e1227

/-- `Equation4417`: `x ◇ (x ◇ y) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxy_pxx_pyx_Equation4417 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4417 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4417.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
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
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
      have b0e69 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e74 : False := by grind
      exact b0e74
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X2) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e32 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) X3) = (M.op X1 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e13 X1 (M.op X1 x) X3
               have i₂ := b4e13 X1 x X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ y) (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e13 X1 x X3
               have i₂ := b4e13 X1 x X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 : G, (M.op y y) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 y X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e39 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e39
            | exact resolve b4e39 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e43 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b4e34 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e34
            | exact resolve b4e34 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e48 : ∀ X1 : G, y = (M.op (M.op X1 y) X1) := by
            intro X1
            first
            | (have i₁ := b4e13 y x X1
               have i₂ := b4e41 x
               grind)
            | exact superpose b4e41 b4e13
            | exact resolve b4e13 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e62 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 y)) X1) = (M.op (M.op X0 y) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X0 y) X0 X1
               have i₂ := b4e48 X0
               grind)
            | exact superpose b4e48 b4e13
            | exact resolve b4e13 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e73 : (σ y) = (M.op y (M.op (σ y) y)) := by
            first
            | (have i₁ := b4e43 (M.op (σ y) y)
               have i₂ := b4e48 (σ y)
               grind)
            | exact superpose b4e48 b4e43
            | exact resolve b4e43 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e89 : y = (M.op y (σ y)) := by
            first
            | (have i₁ := b4e41 (M.op (σ y) y)
               have i₂ := b4e73
               grind)
            | exact superpose b4e73 b4e41
            | exact resolve b4e41 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e105 : (σ y) = (M.op y y) := by
            first
            | (have i₁ := b4e43 y
               have i₂ := b4e89
               grind)
            | exact superpose b4e89 b4e43
            | exact resolve b4e43 b4e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43 b4e89
          have b4e108 : y = (σ y) := by
            first
            | (have i₁ := b4e105
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e105
            | exact resolve b4e105 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e105
          have b4e127 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e108
               grind)
            | exact superpose b4e108 b4e20
            | exact resolve b4e20 b4e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e195 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X2 (M.op X1 X3)) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e35 X2 (M.op X1 X3) X1
               have i₂ := b4e13 X1 X3 X0
               grind)
            | exact superpose b4e13 b4e35
            | exact resolve b4e35 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e201 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y (M.op X1 y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e35 X0 X1 (M.op X1 y)
               have i₂ := b4e48 X1
               grind)
            | exact superpose b4e48 b4e35
            | exact resolve b4e35 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e245 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op y (M.op (M.op X1 X3) y)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e195 X0 X1 x X3
               have i₂ := b4e201 x (M.op X1 X3)
               grind)
            | exact superpose b4e201 b4e195
            | exact resolve b4e195 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e195
          have b4e267 : ∀ X1 X3 : G, (M.op y (M.op (M.op X1 X3) y)) = (M.op (M.op y (M.op X1 y)) X1) := by
            intro X1 X3
            first
            | (have i₁ := b4e245 x X1 X3
               have i₂ := b4e201 x X1
               grind)
            | exact superpose b4e201 b4e245
            | exact resolve b4e245 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e245
          have b4e508 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) X0) = (M.op (M.op y X1) (M.op y y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 y (M.op y X1) X0
               have i₂ := b4e41 X1
               grind)
            | exact superpose b4e41 b4e32
            | exact resolve b4e32 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e533 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X2 (M.op (M.op X3 X1) X3)) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e35 X2 (M.op (M.op X3 X1) X3) X1
               have i₂ := b4e32 X3 X1 X0
               grind)
            | exact superpose b4e32 b4e35
            | exact resolve b4e35 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e542 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op y (M.op (M.op (M.op X3 X1) X3) y)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e533 X0 X1 x X3
               have i₂ := b4e201 x (M.op (M.op X3 X1) X3)
               grind)
            | exact superpose b4e201 b4e533
            | exact resolve b4e533 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e533
          have b4e559 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) X0) = (M.op (M.op y X1) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e508 X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e508
            | exact resolve b4e508 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e508
          have b4e593 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op y (M.op (M.op y (M.op X1 y)) y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e542 X0 X1 x
               have i₂ := b4e201 x X1
               grind)
            | exact superpose b4e201 b4e542
            | exact resolve b4e542 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e542
          have b4e604 : ∀ X0 X1 : G, (M.op y (M.op X1 y)) = (M.op (M.op X0 (M.op y X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e559 X0 X1
               have i₂ := b4e201 y X1
               grind)
            | exact superpose b4e201 b4e559
            | exact resolve b4e559 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e559
          have b4e631 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op y (M.op y y)) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e593 X0 X1
               have i₂ := b4e267 y (M.op X1 y)
               grind)
            | exact superpose b4e267 b4e593
            | exact resolve b4e593 b4e267
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e267 b4e593
          have b4e642 : ∀ X1 : G, (M.op y (M.op X1 y)) = (M.op y (M.op (M.op y X1) y)) := by
            intro X1
            first
            | (have i₁ := b4e604 x X1
               have i₂ := b4e201 x (M.op y X1)
               grind)
            | exact superpose b4e201 b4e604
            | exact resolve b4e604 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e604
          have b4e656 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op y y) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e631 X0 X1
               have i₂ := b4e62 y y
               grind)
            | exact superpose b4e62 b4e631
            | exact resolve b4e631 b4e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62 b4e631
          have b4e660 : ∀ X1 : G, (M.op y (M.op X1 y)) = (M.op y (M.op y (M.op X1 y))) := by
            intro X1
            first
            | (have i₁ := b4e642 X1
               have i₂ := b4e201 y X1
               grind)
            | exact superpose b4e201 b4e642
            | exact resolve b4e642 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e642
          have b4e666 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X1) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e656 X0 X1
               have i₂ := b4e48 y
               grind)
            | exact superpose b4e48 b4e656
            | exact resolve b4e656 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48 b4e656
          have b4e669 : ∀ X1 : G, y = (M.op y (M.op X1 y)) := by
            intro X1
            first
            | (have i₁ := b4e660 X1
               have i₂ := b4e41 (M.op X1 y)
               grind)
            | exact superpose b4e41 b4e660
            | exact resolve b4e660 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e660
          have b4e672 : ∀ X1 : G, y = (M.op (M.op y (M.op X1 y)) X1) := by
            intro X1
            first
            | (have i₁ := b4e666 x X1
               have i₂ := b4e201 x X1
               grind)
            | exact superpose b4e201 b4e666
            | exact resolve b4e666 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e201 b4e666
          have b4e677 : ∀ X1 : G, y = (M.op y X1) := by
            intro X1
            first
            | (have i₁ := b4e672 X1
               have i₂ := b4e669 X1
               grind)
            | exact superpose b4e669 b4e672
            | exact resolve b4e672 b4e669
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e669 b4e672
          have b4e693 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op y y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 y X1 X0
               have i₂ := b4e677 X1
               grind)
            | exact superpose b4e677 b4e32
            | exact resolve b4e32 b4e677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e695 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e35 X0 X1 y
               have i₂ := b4e677 X1
               grind)
            | exact superpose b4e677 b4e35
            | exact resolve b4e35 b4e677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35 b4e677
          have b4e708 : ∀ X0 X1 : G, y = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e695 X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e695
            | exact resolve b4e695 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e695
          have b4e710 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e693 X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e693
            | exact resolve b4e693 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e693
          have b4e714 : ∀ X1 : G, y = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b4e710 x X1
               have i₂ := b4e708 x X1
               grind)
            | exact superpose b4e708 b4e710
            | exact resolve b4e710 b4e708
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e708 b4e710
          have b4e1060 : (σ y) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e127
               have i₂ := b4e714 x
               grind)
            | exact superpose b4e714 b4e127
            | exact resolve b4e127 b4e714
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e127
          have b4e1063 : y ≠ (σ y) := by
            first
            | (have i₁ := b4e1060
               have i₂ := b4e714 (σ x)
               grind)
            | exact superpose b4e714 b4e1060
            | exact resolve b4e1060 b4e714
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e714 b4e1060
          have b4e1077 : False := by grind
          exact b4e1077
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b5e91 : (σ y) ≠ (σ (M.op y y)) := by
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
          have b5e97 : (σ y) ≠ (σ y) := by
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
          have b5e98 : False := by grind
          exact b5e98
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
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e85 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e24
            | exact resolve b7e24 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e94 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e85
               grind)
            | exact superpose b7e85 b7e14
            | exact resolve b7e14 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e95 : y = (M.op y y) := by
            first
            | (have i₁ := b7e94
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e94
            | exact resolve b7e94 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e99 : False := by grind
          exact b7e99
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X2) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e32 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) X3) = (M.op X1 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b8e13 X1 (M.op X1 x) X3
               have i₂ := b8e13 X1 x X0
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e34 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b8e13 X1 x X3
               have i₂ := b8e13 X1 x X0
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X0) X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op X1 X2) X3 X1
               have i₂ := b8e13 X1 X2 X0
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X2 X3 (M.op X2 X0)
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e37 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X0 X1 x
               have i₂ := b8e13 X0 X2 x
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e42 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k (τ X0) X1)
               have i₂ := b8e26 X0 X1
               grind)
            | exact superpose b8e26 b8e14
            | exact resolve b8e14 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e58 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e63 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ y) (M.op (σ y) (σ y))
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (M.op (σ y) (σ y)) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e64 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have j0 := b8e63 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e66 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e58 X0 X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e58
            | (have j0 := b8e58 X0 X1
               grind)
            | exact resolve b8e58 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e72 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e24
            | exact resolve b8e24 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e73 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 (σ X0) X1 (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e13
            | exact resolve b8e13 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e74 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) X1) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 (σ X0) (σ X0) X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e13
            | exact resolve b8e13 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e86 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X2 (M.op X1 X3)) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e34 X2 (M.op X1 X3) X1
               have i₂ := b8e13 X1 X3 X0
               grind)
            | exact superpose b8e13 b8e34
            | exact resolve b8e34 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e89 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 X1) X0) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e34 X2 X3 (M.op X3 X1)
               have i₂ := b8e34 X3 X1 X0
               grind)
            | (have i₁ := b8e34 X2 X3 (M.op X3 X1)
               have i₂ := b8e34 X0 X1 X3
               grind)
            | exact superpose b8e34 b8e34
            | exact resolve b8e34 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e90 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e34 X2 X3 (M.op X3 X0)
               have i₂ := b8e13 X0 X1 X3
               grind)
            | exact superpose b8e13 b8e34
            | exact resolve b8e34 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e99 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X2 X3 (M.op X2 X1)
               have i₂ := b8e34 X2 X1 X0
               grind)
            | (have i₁ := b8e13 X2 X3 (M.op X2 X1)
               have i₂ := b8e34 X0 X1 X2
               grind)
            | exact superpose b8e34 b8e13
            | exact resolve b8e13 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e100 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X3) = (M.op (M.op X2 X1) (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op X2 X1) X2 X3
               have i₂ := b8e34 X2 X1 X0
               grind)
            | (have i₁ := b8e13 (M.op X2 X1) X2 X3
               have i₂ := b8e34 X0 X1 X2
               grind)
            | exact superpose b8e34 b8e13
            | exact resolve b8e13 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e114 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X1 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e37 X1 X2 (M.op X1 x)
               have i₂ := b8e13 X1 x X0
               grind)
            | exact superpose b8e13 b8e37
            | exact resolve b8e37 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e130 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X3 (M.op X0 X2)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e34 X0 (M.op X0 X2) X3
               have i₂ := b8e37 X0 X2 X1
               grind)
            | (have i₁ := b8e34 X0 (M.op X0 X2) X3
               have i₂ := b8e37 X0 X1 X2
               grind)
            | exact superpose b8e37 b8e34
            | exact resolve b8e34 b8e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e131 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X2) (M.op (M.op X0 X2) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op X0 X2) X3 X0
               have i₂ := b8e37 X0 X2 X1
               grind)
            | (have i₁ := b8e13 (M.op X0 X2) X3 X0
               have i₂ := b8e37 X0 X1 X2
               grind)
            | exact superpose b8e37 b8e13
            | exact resolve b8e13 b8e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e154 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) = (M.op X2 (M.op (M.op X3 X2) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e32 X3 X2 (M.op X2 X1)
               have i₂ := b8e34 X2 X1 X0
               grind)
            | (have i₁ := b8e32 X3 X2 (M.op X2 X1)
               have i₂ := b8e34 X0 X1 X2
               grind)
            | exact superpose b8e34 b8e32
            | exact resolve b8e32 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34
          have b8e156 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X1 (σ X0) (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e32
            | exact resolve b8e32 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e205 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e42 X0 y
               have i₂ := b8e64 X0
               grind)
            | exact superpose b8e64 b8e42
            | (have j1 := b8e64 X0
               grind)
            | exact resolve b8e42 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42 b8e64
          have b8e485 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) (M.op (M.op (σ X0) X1) X2)) = (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e35 (σ X0) (σ X0) X1 X2
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e35
            | exact resolve b8e35 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e704 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b8e74 X0 (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e74
            | exact resolve b8e74 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e737 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 (M.op X1 (σ X0))) X3) (M.op X1 (σ X0))) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op (M.op (σ X0) (σ (M.op X0 X0))) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e35 X0 (M.op X1 (σ X0)) X1 X3
               have i₂ := b8e74 X0 X1
               grind)
            | exact superpose b8e74 b8e35
            | exact resolve b8e35 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e763 : ∀ X0 X1 X3 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) = (M.op (M.op (M.op X3 (M.op X1 (σ X0))) X3) (M.op X1 (σ X0))) := by
            intro X0 X1 X3
            first
            | (have i₁ := b8e737 X0 X1 x X3
               have i₂ := b8e485 X0 (σ (M.op X0 X0)) x
               grind)
            | exact superpose b8e485 b8e737
            | exact resolve b8e737 b8e485
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e485 b8e737
          have b8e772 : ∀ X0 X1 X3 : G, (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ X0)) = (M.op (M.op (M.op X3 (M.op X1 (σ X0))) X3) (M.op X1 (σ X0))) := by
            intro X0 X1 X3
            first
            | (have i₁ := b8e763 X0 X1 X3
               have i₂ := b8e704 X0
               grind)
            | exact superpose b8e704 b8e763
            | exact resolve b8e763 b8e704
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e704 b8e763
          have b8e1102 : ∀ X0 : G, (k (τ (σ (M.op y y))) y) = (τ (M.op (M.op X0 (σ y)) X0)) ∨ (σ y) = (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b8e205 (σ (M.op y y))
               have i₂ := b8e74 y X0
               grind)
            | exact superpose b8e74 b8e205
            | (have j0 := b8e205 (σ (M.op y y))
               grind)
            | exact resolve b8e205 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e205
          have b8e1122 : ∀ X0 : G, (k (τ (σ (M.op y y))) y) = (τ (M.op (M.op X0 (σ y)) X0)) := by
            intro X0
            first
            | (have j0 := b8e1102 X0
               grind)
            | (have r₁ := b8e1102 X0
               have r₂ := b8e72
               grind)
            | exact resolve b8e1102 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72 b8e1102
          have b8e1124 : ∀ X0 : G, (τ (M.op (M.op X0 (σ y)) X0)) = (k (M.op y y) y) := by
            intro X0
            first
            | (have i₁ := b8e1122 X0
               have i₂ := b8e14 (M.op y y)
               grind)
            | exact superpose b8e14 b8e1122
            | exact resolve b8e1122 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1122
          have b8e1142 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e66 x y
               grind)
            | exact superpose b8e66 b8e20
            | (have j1 := b8e66 x (M.op x x)
               grind)
            | exact resolve b8e20 b8e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e1191 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e1142
               have r₂ := b8e23
               grind)
            | exact resolve b8e1142 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1142
          have b8e1238 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (σ (k (M.op y y) y)) := by
            intro X0
            first
            | (have i₁ := b8e15 (M.op (M.op X0 (σ y)) X0)
               have i₂ := b8e1124 X0
               grind)
            | exact superpose b8e1124 b8e15
            | exact resolve b8e15 b8e1124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1124
          have b8e1333 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (σ (M.op y (M.op y y))) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b8e1238 X0
               have i₂ := b8e18 (M.op y y) y
               grind)
            | exact superpose b8e18 b8e1238
            | (have j1 := b8e18 (M.op y y) y
               grind)
            | exact resolve b8e1238 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1337 : (M.op (σ y) (σ (M.op y y))) = (σ (k (M.op y y) y)) := by
            first
            | (have i₁ := b8e74 y x
               have i₂ := b8e1238 x
               grind)
            | exact superpose b8e1238 b8e74
            | exact resolve b8e74 b8e1238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e1383 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (σ (M.op y (M.op y y))) ∨ y = (M.op y y) := by
            intro X0
            first
            | (have j0 := b8e1333 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1333
          have b8e1391 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (σ (M.op y (M.op y y))) := by
            intro X0
            first
            | (have j0 := b8e1383 X0
               grind)
            | (have r₁ := b8e1383 X0
               have r₂ := b8e22
               grind)
            | exact resolve b8e1383 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1383
          have b8e1502 : (σ (k (M.op y y) y)) = (σ (M.op y (M.op y y))) := by
            first
            | (have i₁ := b8e1238 x
               have i₂ := b8e1391 x
               grind)
            | exact superpose b8e1391 b8e1238
            | exact resolve b8e1238 b8e1391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1238
          have b8e2173 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 (σ y))) X0) (M.op X1 (σ y))) = (M.op (M.op X2 (σ (M.op y (M.op y y)))) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e86 X0 (M.op X1 (σ y)) X2 X1
               have i₂ := b8e1391 X1
               grind)
            | exact superpose b8e1391 b8e86
            | exact resolve b8e86 b8e1391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2308 : ∀ X2 : G, (M.op (M.op (σ y) (σ (M.op y y))) (σ y)) = (M.op (M.op X2 (σ (M.op y (M.op y y)))) X2) := by
            intro X2
            first
            | (have i₁ := b8e2173 x x X2
               have i₂ := b8e772 y x x
               grind)
            | exact superpose b8e772 b8e2173
            | exact resolve b8e2173 b8e772
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e772 b8e2173
          have b8e2330 : ∀ X2 : G, (M.op (σ (k (M.op y y) y)) (σ y)) = (M.op (M.op X2 (σ (M.op y (M.op y y)))) X2) := by
            intro X2
            first
            | (have i₁ := b8e2308 X2
               have i₂ := b8e1337
               grind)
            | exact superpose b8e1337 b8e2308
            | exact resolve b8e2308 b8e1337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1337 b8e2308
          have b8e2337 : ∀ X2 : G, (M.op (σ (M.op y (M.op y y))) (σ y)) = (M.op (M.op X2 (σ (M.op y (M.op y y)))) X2) := by
            intro X2
            first
            | (have i₁ := b8e2330 X2
               have i₂ := b8e1502
               grind)
            | exact superpose b8e1502 b8e2330
            | exact resolve b8e2330 b8e1502
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2330
          have b8e6027 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e1191
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e1191
            | (have j1 := b8e18 (M.op x x) x
               grind)
            | (have r₁ := b8e1191
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e1191
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e1191 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1191
          have b8e6028 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by grind
          clear b8e6027
          have b8e6030 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
            first
            | (have r₁ := b8e6028
               have r₂ := b8e21
               grind)
            | exact resolve b8e6028 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6028
          have b8e6037 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e14 (M.op x x)
               have i₂ := b8e6030
               grind)
            | exact superpose b8e6030 b8e14
            | exact resolve b8e14 b8e6030
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6030
          have b8e6072 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e6037
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e6037
            | exact resolve b8e6037 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6037
          have b8e6073 : x = (M.op x x) := by grind
          clear b8e6072
          have b8e6170 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ (M.op y (M.op y y)))) X0) = (M.op (σ (M.op y (M.op y y))) (M.op (M.op X2 X1) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e100 X0 X0 (M.op X0 (σ y)) x
               have i₂ := b8e1391 X0
               grind)
            | exact superpose b8e1391 b8e100
            | exact resolve b8e100 b8e1391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e100 b8e1391
          have b8e6528 : ∀ X1 X2 : G, (M.op (σ (M.op y (M.op y y))) (σ y)) = (M.op (σ (M.op y (M.op y y))) (M.op (M.op X2 X1) X2)) := by
            intro X1 X2
            first
            | (have i₁ := b8e6170 x X1 X2
               have i₂ := b8e2337 x
               grind)
            | exact superpose b8e2337 b8e6170
            | exact resolve b8e6170 b8e2337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2337 b8e6170
          have b8e6565 : ∀ X0 : G, (M.op x x) = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b8e37 x X0 x
               have i₂ := b8e6073
               grind)
            | exact superpose b8e6073 b8e37
            | exact resolve b8e37 b8e6073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37
          have b8e6572 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x x) (M.op X1 x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e90 x x X0 X1
               have i₂ := b8e6073
               grind)
            | exact superpose b8e6073 b8e90
            | exact resolve b8e90 b8e6073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e6574 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x x) (M.op X0 x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e99 x x X0 X1
               have i₂ := b8e6073
               grind)
            | exact superpose b8e6073 b8e99
            | exact resolve b8e99 b8e6073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e6590 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op X0 x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e6574 X0 X1
               have i₂ := b8e6073
               grind)
            | exact superpose b8e6073 b8e6574
            | exact resolve b8e6574 b8e6073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6574
          have b8e6591 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x (M.op X1 x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e6572 X0 X1
               have i₂ := b8e6073
               grind)
            | exact superpose b8e6073 b8e6572
            | exact resolve b8e6572 b8e6073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6572
          have b8e6594 : ∀ X0 : G, x = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b8e6565 X0
               have i₂ := b8e6073
               grind)
            | exact superpose b8e6073 b8e6565
            | exact resolve b8e6565 b8e6073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6565
          have b8e6856 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) X3) = (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2)) (M.op X4 (M.op X0 X5))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e89 X0 (M.op X0 X5) X3 X4
               have i₂ := b8e131 X0 X5 X1 X2
               grind)
            | exact superpose b8e131 b8e89
            | exact resolve b8e89 b8e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89
          have b8e6906 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X0 X4)) X0) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op (M.op X0 X1) X2) X3)) (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e130 X0 X4 X1 (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5))
               have i₂ := b8e131 (M.op X0 X1) X5 X2 X3
               grind)
            | exact superpose b8e131 b8e130
            | exact resolve b8e130 b8e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e6907 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X4 X0) X4) X0) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op (M.op X0 X1) X2) X3)) (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e86 X4 X0 (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5)) X1
               have i₂ := b8e131 (M.op X0 X1) X5 X2 X3
               grind)
            | exact superpose b8e131 b8e86
            | exact resolve b8e86 b8e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e86
          have b8e6927 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X4 X0) X4) X0) = (M.op (M.op X0 X2) (M.op (M.op X0 (M.op X0 X1)) X0)) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b8e35 X4 X0 X2 (M.op (M.op X0 X2) x)
               have i₂ := b8e131 X0 X1 X2 x
               grind)
            | exact superpose b8e131 b8e35
            | exact resolve b8e35 b8e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35 b8e131
          have b8e7014 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X4 X0) X4) X0) = (M.op (M.op X0 X2) (M.op x (M.op (M.op X0 X1) x))) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b8e6927 X0 X1 X2 X4
               have i₂ := b8e6591 X0 (M.op X0 X1)
               grind)
            | exact superpose b8e6591 b8e6927
            | exact resolve b8e6927 b8e6591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6927
          have b8e7030 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X4 X0) X4) X0) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op (M.op X0 X1) X2) X3)) (M.op x (M.op (M.op X0 X1) x))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e6907 X0 X1 X2 X3 X4 x
               have i₂ := b8e6590 (M.op X0 X1) x
               grind)
            | exact superpose b8e6590 b8e6907
            | exact resolve b8e6907 b8e6590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6907
          have b8e7031 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X0 X4)) X0) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op (M.op X0 X1) X2) X3)) (M.op x (M.op (M.op X0 X1) x))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e6906 X0 X1 X2 X3 X4 x
               have i₂ := b8e6590 (M.op X0 X1) x
               grind)
            | exact superpose b8e6590 b8e6906
            | exact resolve b8e6906 b8e6590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6906
          have b8e7064 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op X3 X4) X3) = (M.op (M.op x (M.op (M.op X0 X1) x)) (M.op X4 (M.op X0 X5))) := by
            intro X0 X1 X3 X4 X5
            first
            | (have i₁ := b8e6856 X0 X1 x X3 X4 X5
               have i₂ := b8e6590 (M.op X0 X1) x
               grind)
            | exact superpose b8e6590 b8e6856
            | exact resolve b8e6856 b8e6590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6856
          have b8e7209 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op x (M.op (M.op X0 X1) x))) = (M.op (M.op x (M.op X0 x)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e7014 X0 X1 X2 x
               have i₂ := b8e6591 x X0
               grind)
            | exact superpose b8e6591 b8e7014
            | exact resolve b8e7014 b8e6591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7014
          have b8e7224 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X4 X0) X4) X0) = (M.op (M.op x (M.op (M.op (M.op X0 X1) X2) x)) (M.op x (M.op (M.op X0 X1) x))) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b8e7030 X0 X1 X2 x X4
               have i₂ := b8e6590 (M.op (M.op X0 X1) X2) x
               grind)
            | exact superpose b8e6590 b8e7030
            | exact resolve b8e7030 b8e6590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7030
          have b8e7225 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 (M.op X0 X4)) X0) = (M.op (M.op x (M.op (M.op (M.op X0 X1) X2) x)) (M.op x (M.op (M.op X0 X1) x))) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b8e7031 X0 X1 X2 x X4
               have i₂ := b8e6590 (M.op (M.op X0 X1) X2) x
               grind)
            | exact superpose b8e6590 b8e7031
            | exact resolve b8e7031 b8e6590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7031
          have b8e7252 : ∀ X0 X1 X4 X5 : G, (M.op (M.op x (M.op (M.op X0 X1) x)) (M.op X4 (M.op X0 X5))) = (M.op x (M.op X4 x)) := by
            intro X0 X1 X4 X5
            first
            | (have i₁ := b8e7064 X0 X1 x X4 X5
               have i₂ := b8e6591 x X4
               grind)
            | exact superpose b8e6591 b8e7064
            | exact resolve b8e7064 b8e6591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7064
          have b8e7376 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op X0 x)) X0) = (M.op (M.op x (M.op (M.op (M.op X0 X1) X2) x)) (M.op x (M.op (M.op X0 X1) x))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e7224 X0 X1 X2 x
               have i₂ := b8e6591 x X0
               grind)
            | exact superpose b8e6591 b8e7224
            | exact resolve b8e7224 b8e6591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7224
          have b8e7377 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x (M.op (M.op (M.op X0 X1) X2) x)) (M.op x (M.op (M.op X0 X1) x))) = (M.op x (M.op (M.op X0 X4) x)) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b8e7225 X0 X1 X2 X4
               have i₂ := b8e6591 X0 (M.op X0 X4)
               grind)
            | exact superpose b8e6591 b8e7225
            | exact resolve b8e7225 b8e6591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7225
          have b8e7447 : ∀ X0 : G, (M.op x (M.op x x)) = (M.op (M.op x (M.op X0 x)) X0) := by
            intro X0
            first
            | (have i₁ := b8e7376 X0 x x
               have i₂ := b8e7252 (M.op X0 x) x x x
               grind)
            | exact superpose b8e7252 b8e7376
            | exact resolve b8e7376 b8e7252
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7376
          have b8e7448 : ∀ X0 X4 : G, (M.op x (M.op x x)) = (M.op x (M.op (M.op X0 X4) x)) := by
            intro X0 X4
            first
            | (have i₁ := b8e7377 X0 x x X4
               have i₂ := b8e7252 (M.op X0 x) x x x
               grind)
            | exact superpose b8e7252 b8e7377
            | exact resolve b8e7377 b8e7252
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7377
          have b8e7492 : ∀ X0 : G, x = (M.op (M.op x (M.op X0 x)) X0) := by
            intro X0
            first
            | (have i₁ := b8e7447 X0
               have i₂ := b8e6594 x
               grind)
            | exact superpose b8e6594 b8e7447
            | exact resolve b8e7447 b8e6594
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7447
          have b8e7493 : ∀ X0 X4 : G, x = (M.op x (M.op (M.op X0 X4) x)) := by
            intro X0 X4
            first
            | (have i₁ := b8e7448 X0 X4
               have i₂ := b8e6594 x
               grind)
            | exact superpose b8e6594 b8e7448
            | exact resolve b8e7448 b8e6594
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7448
          have b8e7555 : ∀ X1 X2 : G, x = (M.op (M.op X1 (M.op X1 X2)) (M.op x X1)) := by
            intro X1 X2
            first
            | (have i₁ := b8e36 X1 X2 x x
               have i₂ := b8e6594 x
               grind)
            | exact superpose b8e6594 b8e36
            | exact resolve b8e36 b8e6594
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36
          have b8e7590 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op (M.op x X0) X1)) = (M.op (M.op x X0) (M.op x x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e114 x (M.op x X0) X1
               have i₂ := b8e6594 X0
               grind)
            | exact superpose b8e6594 b8e114
            | exact resolve b8e114 b8e6594
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e114
          have b8e7607 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op (M.op x X0) X1)) = (M.op (M.op x X0) x) := by
            intro X0 X1
            first
            | (have i₁ := b8e7590 X0 X1
               have i₂ := b8e6073
               grind)
            | exact superpose b8e6073 b8e7590
            | exact resolve b8e7590 b8e6073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6073 b8e7590
          have b8e7651 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op (M.op x X0) X1)) = (M.op x (M.op X0 x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e7607 X0 X1
               have i₂ := b8e6591 x X0
               grind)
            | exact superpose b8e6591 b8e7607
            | exact resolve b8e7607 b8e6591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7607
          have b8e7676 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op x (M.op (M.op x X0) x)) := by
            intro X0
            first
            | (have i₁ := b8e7651 X0 x
               have i₂ := b8e6590 (M.op x X0) x
               grind)
            | exact superpose b8e6590 b8e7651
            | exact resolve b8e7651 b8e6590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7651
          have b8e7687 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b8e7676 X0
               have i₂ := b8e7493 x X0
               grind)
            | exact superpose b8e7493 b8e7676
            | exact resolve b8e7676 b8e7493
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7676
          have b8e7779 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X4 (M.op (M.op X5 X4) X5)) = (M.op (M.op (M.op X0 (M.op X1 X2)) X0) (M.op X4 (M.op X1 X3))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e154 X1 (M.op X1 X3) X4 X5
               have i₂ := b8e130 X1 X3 X2 X0
               grind)
            | (have i₁ := b8e154 X3 (M.op X0 X2) X2 X3
               have i₂ := b8e130 X0 X1 X2 X3
               grind)
            | exact superpose b8e130 b8e154
            | exact resolve b8e154 b8e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130
          have b8e8049 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 X0) X0)) (M.op (σ (M.op (M.op X0 X0) X0)) X2)) = (M.op (σ (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X0 X0)) X1))) (σ (M.op (M.op X0 X0) X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e73 (M.op (M.op X0 X0) X0) X2
               have i₂ := b8e154 X0 X0 (M.op X0 X0) X1
               grind)
            | exact superpose b8e154 b8e73
            | exact resolve b8e73 b8e154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e8128 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X4 (M.op (M.op X5 X2) X5)) X4) (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e99 X4 (M.op (M.op X5 X2) X5) X2 X3
               have i₂ := b8e154 X0 X1 X2 X5
               grind)
            | exact superpose b8e154 b8e99
            | exact resolve b8e99 b8e154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99 b8e154
          have b8e8170 : ∀ X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X4 (M.op (M.op X5 X2) X5)) X4) (M.op (M.op x (M.op X1 x)) (M.op X2 X1))) := by
            intro X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e8128 x X1 X2 X3 X4 X5
               have i₂ := b8e6591 x X1
               grind)
            | exact superpose b8e6591 b8e8128
            | exact resolve b8e8128 b8e6591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8128
          have b8e8232 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X0 X0)) X1))) (σ (M.op x (M.op X0 x)))) = (M.op (σ (M.op x (M.op X0 x))) (M.op (σ (M.op x (M.op X0 x))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e8049 X1 X1 X2
               have i₂ := b8e6591 X1 X1
               grind)
            | exact superpose b8e6591 b8e8049
            | exact resolve b8e8049 b8e6591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8049
          have b8e8382 : ∀ X1 X2 X3 X4 X5 : G, (M.op X4 (M.op (M.op X5 X4) X5)) = (M.op (M.op x (M.op (M.op X1 X2) x)) (M.op X4 (M.op X1 X3))) := by
            intro X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e7779 x X1 X2 X3 X4 X5
               have i₂ := b8e6591 x (M.op X1 X2)
               grind)
            | exact superpose b8e6591 b8e7779
            | exact resolve b8e7779 b8e6591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7779
          have b8e8453 : ∀ X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X4 (M.op (M.op X5 X2) X5)) X4) (M.op x (M.op X2 X1))) := by
            intro X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e8170 X1 X2 X3 X4 X5
               have i₂ := b8e7687 X1
               grind)
            | exact superpose b8e7687 b8e8170
            | exact resolve b8e8170 b8e7687
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8170
          have b8e8514 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X0 X0)) X1))) (σ (M.op x (M.op X0 x)))) = (M.op x (M.op (σ (M.op x (M.op X0 x))) x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e8232 X0 X1 x
               have i₂ := b8e6590 (σ (M.op x (M.op X0 x))) x
               grind)
            | exact superpose b8e6590 b8e8232
            | exact resolve b8e8232 b8e6590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8232
          have b8e8661 : ∀ X4 X5 : G, (M.op x (M.op X4 x)) = (M.op X4 (M.op (M.op X5 X4) X5)) := by
            intro X4 X5
            first
            | (have i₁ := b8e8382 x x x X4 X5
               have i₂ := b8e7252 x x X4 x
               grind)
            | exact superpose b8e7252 b8e8382
            | exact resolve b8e8382 b8e7252
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7252 b8e8382
          have b8e8727 : ∀ X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op (M.op (M.op X5 X2) X5) x)) (M.op x (M.op X2 X1))) := by
            intro X1 X2 X3 X5
            first
            | (have i₁ := b8e8453 X1 X2 X3 x X5
               have i₂ := b8e6591 x (M.op (M.op X5 X2) X5)
               grind)
            | exact superpose b8e6591 b8e8453
            | exact resolve b8e8453 b8e6591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8453
          have b8e8788 : ∀ X0 X1 : G, x = (M.op (σ (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X0 X0)) X1))) (σ (M.op x (M.op X0 x)))) := by
            intro X0 X1
            first
            | (have i₁ := b8e8514 X0 X1
               have i₂ := b8e7687 (σ (M.op x (M.op X0 x)))
               grind)
            | exact superpose b8e7687 b8e8514
            | exact resolve b8e8514 b8e7687
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8514
          have b8e8914 : ∀ X4 : G, (M.op x (M.op X4 x)) = (M.op X4 (M.op x (M.op X4 x))) := by
            intro X4
            first
            | (have i₁ := b8e8661 X4 x
               have i₂ := b8e6591 x X4
               grind)
            | exact superpose b8e6591 b8e8661
            | exact resolve b8e8661 b8e6591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8661
          have b8e8965 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op x (M.op x (M.op X2 X1))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e8727 X1 X2 X3 x
               have i₂ := b8e7493 (M.op x X2) x
               grind)
            | exact superpose b8e7493 b8e8727
            | exact resolve b8e8727 b8e7493
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7493 b8e8727
          have b8e9024 : ∀ X0 X1 : G, x = (M.op (σ (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X0 X0)) X1))) (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e8788 X0 X1
               have i₂ := b8e7687 X0
               grind)
            | exact superpose b8e7687 b8e8788
            | exact resolve b8e8788 b8e7687
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8788
          have b8e9141 : ∀ X4 : G, x = (M.op X4 x) := by
            intro X4
            first
            | (have i₁ := b8e8914 x
               have i₂ := b8e7687 x
               grind)
            | exact superpose b8e7687 b8e8914
            | exact resolve b8e8914 b8e7687
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7687 b8e8914
          have b8e9187 : ∀ X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op x (M.op x x)) := by
            intro X2 X3
            first
            | (have i₁ := b8e8965 x X2 X3
               have i₂ := b8e6590 x (M.op X2 x)
               grind)
            | exact superpose b8e6590 b8e8965
            | exact resolve b8e8965 b8e6590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6590 b8e8965
          have b8e9236 : ∀ X0 : G, x = (M.op (σ (M.op (M.op X0 X0) (M.op x (M.op (M.op X0 X0) x)))) (σ x)) := by
            intro X0
            first
            | (have i₁ := b8e9024 X0 x
               have i₂ := b8e6591 x (M.op X0 X0)
               grind)
            | exact superpose b8e6591 b8e9024
            | exact resolve b8e9024 b8e6591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6591 b8e9024
          have b8e9346 : ∀ X2 X3 : G, x = (M.op X2 (M.op X2 X3)) := by
            intro X2 X3
            first
            | (have i₁ := b8e9187 X2 X3
               have i₂ := b8e6594 x
               grind)
            | exact superpose b8e6594 b8e9187
            | exact resolve b8e9187 b8e6594
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6594 b8e9187
          have b8e9380 : ∀ X0 : G, x = (M.op (σ (M.op (M.op x (M.op X0 x)) X0)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b8e9236 X0
               have i₂ := b8e7209 X0 X0 X0
               grind)
            | exact superpose b8e7209 b8e9236
            | exact resolve b8e9236 b8e7209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7209 b8e9236
          have b8e9484 : x = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e9380 x
               have i₂ := b8e7492 x
               grind)
            | exact superpose b8e7492 b8e9380
            | exact resolve b8e9380 b8e7492
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7492 b8e9380
          have b8e9539 : x = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e9484
               have i₂ := b8e30 x
               grind)
            | exact superpose b8e30 b8e9484
            | exact resolve b8e9484 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e9484
          have b8e9554 : x = (σ x) := by
            first
            | (have i₁ := b8e9539
               have i₂ := b8e9141 x
               grind)
            | exact superpose b8e9141 b8e9539
            | exact resolve b8e9539 b8e9141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9539
          have b8e9556 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e9554
               grind)
            | exact superpose b8e9554 b8e20
            | exact resolve b8e20 b8e9554
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11099 : ∀ X0 : G, (M.op (σ (M.op (k (M.op y y) y) (k (M.op y y) y))) (σ (M.op y (M.op y y)))) = (M.op (σ (M.op y (M.op y y))) (M.op (M.op X0 (σ (M.op y (M.op y y)))) X0)) := by
            intro X0
            first
            | (have i₁ := b8e156 (k (M.op y y) y) x
               have i₂ := b8e1502
               grind)
            | exact superpose b8e1502 b8e156
            | exact resolve b8e156 b8e1502
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156 b8e1502
          have b8e11402 : (M.op (σ (M.op y (M.op y y))) (σ y)) = (M.op (σ (M.op (k (M.op y y) y) (k (M.op y y) y))) (σ (M.op y (M.op y y)))) := by
            first
            | (have i₁ := b8e11099 x
               have i₂ := b8e6528 (σ (M.op y (M.op y y))) x
               grind)
            | exact superpose b8e6528 b8e11099
            | exact resolve b8e11099 b8e6528
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6528 b8e11099
          have b8e11537 : (M.op (σ x) (σ y)) = (M.op (σ (M.op (k (M.op y y) y) (k (M.op y y) y))) (σ x)) := by
            first
            | (have i₁ := b8e11402
               have i₂ := b8e9346 y y
               grind)
            | exact superpose b8e9346 b8e11402
            | exact resolve b8e11402 b8e9346
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9346 b8e11402
          have b8e11654 : (M.op x (σ y)) = (M.op (σ (M.op (k (M.op y y) y) (k (M.op y y) y))) x) := by
            first
            | (have i₁ := b8e11537
               have i₂ := b8e9554
               grind)
            | exact superpose b8e9554 b8e11537
            | exact resolve b8e11537 b8e9554
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11537
          have b8e11753 : x = (M.op x (σ y)) := by
            first
            | (have i₁ := b8e11654
               have i₂ := b8e9141 (σ (M.op (k (M.op y y) y) (k (M.op y y) y)))
               grind)
            | exact superpose b8e9141 b8e11654
            | exact resolve b8e11654 b8e9141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11654
          have b8e13483 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op X1 (M.op X1 X2)) (M.op x X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e90 X1 X2 X0 x
               have i₂ := b8e9141 X0
               grind)
            | exact superpose b8e9141 b8e90
            | exact resolve b8e90 b8e9141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90 b8e9141
          have b8e13598 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b8e13483 X0 x x
               have i₂ := b8e7555 x x
               grind)
            | exact superpose b8e7555 b8e13483
            | exact resolve b8e13483 b8e7555
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7555 b8e13483
          have b8e61138 : (σ x) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b8e9556
               have i₂ := b8e13598 y
               grind)
            | exact superpose b8e13598 b8e9556
            | exact resolve b8e9556 b8e13598
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9556 b8e13598
          have b8e61139 : x ≠ (σ x) := by
            first
            | (have i₁ := b8e61138
               have i₂ := b8e11753
               grind)
            | exact superpose b8e11753 b8e61138
            | exact resolve b8e61138 b8e11753
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11753 b8e61138
          have b8e61140 : False := by grind
          exact b8e61140

/-- `Equation4428`: `x ◇ (x ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pxy_Equation4428 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4428 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4428.models_iff G M).mp hM
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
      have b0e65 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e68 : False := by grind
      exact b0e68
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
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
            intro X0 X1 X2 X3
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
          have b4e32 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e13 X3 (M.op X3 X2) X4 X5
               have i₂ := b4e13 X3 X2 X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) X1) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e13 (M.op X2 X3) X1 X4 X5
               have i₂ := b4e13 X0 X1 X2 X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X1 : G, (M.op (σ y) X1) = (M.op y X1) := by
            intro X1
            first
            | (have i₁ := b4e39 x X1
               have i₂ := b4e40 x X1
               grind)
            | exact superpose b4e40 b4e39
            | exact resolve b4e39 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e45 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) X1) = (M.op (M.op X2 X3) (M.op y X1)) := by
            intro X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e33 x X1 X2 X3 X4 X5
               have i₂ := b4e40 x X1
               grind)
            | exact superpose b4e40 b4e33
            | exact resolve b4e33 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e48 : (σ y) = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e24
               have i₂ := b4e43 (σ x)
               grind)
            | exact superpose b4e43 b4e24
            | exact resolve b4e24 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e73 : ∀ X0 X1 : G, (M.op y (M.op X1 X0)) = (M.op X1 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e40 X1 (M.op X1 X0)
               have i₂ := b4e40 X1 X0
               grind)
            | exact superpose b4e40 b4e40
            | exact resolve b4e40 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e83 : ∀ X0 X2 X3 : G, (M.op y X0) = (M.op (M.op X2 X3) X0) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e13 x X0 X2 X3
               have i₂ := b4e40 x X0
               grind)
            | exact superpose b4e40 b4e13
            | exact resolve b4e13 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e86 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op y X0)) = (M.op (M.op X2 X3) (M.op X1 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 (M.op X1 X0) X2 X3
               have i₂ := b4e40 X1 X0
               grind)
            | exact superpose b4e40 b4e13
            | exact resolve b4e13 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e155 : ∀ X0 X1 : G, (M.op y X1) = (M.op (σ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e83 X1 (σ X0) (σ X0)
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e83
            | exact resolve b4e83 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e156 : ∀ X0 : G, (M.op y (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e40 (σ X0) (σ X0)
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e40
            | exact resolve b4e40 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e552 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (σ (M.op y (M.op X0 X1))) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e155 (M.op X0 X1) X2
               have i₂ := b4e83 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b4e83 b4e155
            | exact resolve b4e155 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e564 : ∀ X0 : G, (M.op y (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e30 (M.op X0 X0)
               have i₂ := b4e155 X0 (σ (M.op X0 X0))
               grind)
            | exact superpose b4e155 b4e30
            | exact resolve b4e30 b4e155
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e587 : ∀ X0 : G, (M.op y (σ (M.op X0 X0))) = (σ (M.op X0 (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b4e564 X0
               have i₂ := b4e86 X0 X0 X0 X0
               grind)
            | exact superpose b4e86 b4e564
            | exact resolve b4e564 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e564
          have b4e689 : ∀ X0 X1 X2 X3 : G, (M.op y X3) = (M.op (σ (M.op (M.op X0 X1) X2)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e155 (M.op y X2) X3
               have i₂ := b4e45 X2 y X2 X0 X1
               grind)
            | exact superpose b4e45 b4e155
            | exact resolve b4e155 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e155
          have b4e690 : ∀ X2 X3 : G, (M.op y X3) = (M.op (σ (M.op y X2)) X3) := by
            intro X2 X3
            first
            | (have i₁ := b4e689 x x X2 X3
               have i₂ := b4e83 X2 x x
               grind)
            | exact superpose b4e83 b4e689
            | exact resolve b4e689 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e689
          have b4e931 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 X5) (M.op X6 (M.op X0 X3))) = (M.op X6 (M.op X0 (M.op (M.op X1 X2) X3))) := by
            intro X0 X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b4e32 x x (M.op X0 X3) X6 X4 X5
               have i₂ := b4e32 X1 X2 X3 X0 x x
               grind)
            | (have i₁ := b4e32 X0 X1 (M.op (M.op X0 X1) X2) X3 X4 X5
               have i₂ := b4e32 X0 X1 X2 (M.op X0 X1) X4 X5
               grind)
            | exact superpose b4e32 b4e32
            | exact resolve b4e32 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e952 : ∀ X0 X1 X2 X3 X6 X7 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op X6 X7) (M.op y (M.op X0 X3))) := by
            intro X0 X1 X2 X3 X6 X7
            first
            | (have i₁ := b4e45 (M.op X0 X3) X6 X7 x x
               have i₂ := b4e32 X1 X2 X3 X0 x x
               grind)
            | (have i₁ := b4e45 (M.op (M.op X0 X1) X2) X2 X3 x x
               have i₂ := b4e32 X0 X1 X2 (M.op x x) x x
               grind)
            | exact superpose b4e32 b4e45
            | exact resolve b4e45 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32 b4e45
          have b4e1031 : ∀ X0 X1 X2 X3 X6 X7 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op y (M.op (M.op X6 X7) (M.op X0 X3))) := by
            intro X0 X1 X2 X3 X6 X7
            first
            | (have i₁ := b4e952 X0 X1 X2 X3 X6 X7
               have i₂ := b4e73 (M.op X0 X3) (M.op X6 X7)
               grind)
            | exact superpose b4e73 b4e952
            | exact resolve b4e952 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e952
          have b4e1051 : ∀ X0 X3 X4 X5 X6 : G, (M.op (M.op X4 X5) (M.op X6 (M.op X0 X3))) = (M.op X6 (M.op X0 (M.op y X3))) := by
            intro X0 X3 X4 X5 X6
            first
            | (have i₁ := b4e931 X0 x x X3 X4 X5 X6
               have i₂ := b4e83 X3 x x
               grind)
            | exact superpose b4e83 b4e931
            | exact resolve b4e931 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e931
          have b4e1125 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op y (M.op X0 (M.op y X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e1031 X0 X1 X2 X3 x x
               have i₂ := b4e86 X3 X0 x x
               grind)
            | exact superpose b4e86 b4e1031
            | exact resolve b4e1031 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1031
          have b4e1142 : ∀ X0 X3 X6 : G, (M.op X6 (M.op X0 (M.op y X3))) = (M.op X6 (M.op y (M.op X0 X3))) := by
            intro X0 X3 X6
            first
            | (have i₁ := b4e1051 X0 X3 x x X6
               have i₂ := b4e86 (M.op X0 X3) X6 x x
               grind)
            | exact superpose b4e86 b4e1051
            | exact resolve b4e1051 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1051
          have b4e1192 : ∀ X0 X3 : G, (M.op X0 (M.op y X3)) = (M.op y (M.op X0 (M.op y X3))) := by
            intro X0 X3
            first
            | (have i₁ := b4e1125 X0 x x X3
               have i₂ := b4e83 X3 x x
               grind)
            | exact superpose b4e83 b4e1125
            | exact resolve b4e1125 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1125
          have b4e2039 : ∀ X0 : G, (σ (M.op (M.op y X0) (M.op y X0))) = (M.op y (σ (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b4e30 (M.op y X0)
               have i₂ := b4e690 X0 (σ (M.op y X0))
               grind)
            | exact superpose b4e690 b4e30
            | exact resolve b4e30 b4e690
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e690
          have b4e2079 : ∀ X0 : G, (M.op y (σ (M.op y X0))) = (σ (M.op y (M.op (M.op y X0) X0))) := by
            intro X0
            first
            | (have i₁ := b4e2039 X0
               have i₂ := b4e73 X0 (M.op y X0)
               grind)
            | exact superpose b4e73 b4e2039
            | exact resolve b4e2039 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2039
          have b4e2091 : ∀ X0 : G, (σ (M.op y (M.op y X0))) = (M.op y (σ (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b4e2079 X0
               have i₂ := b4e83 X0 y X0
               grind)
            | exact superpose b4e83 b4e2079
            | exact resolve b4e2079 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83 b4e2079
          have b4e2094 : ∀ X0 : G, (σ (M.op y X0)) = (M.op y (σ (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b4e2091 X0
               have i₂ := b4e40 y X0
               grind)
            | exact superpose b4e40 b4e2091
            | exact resolve b4e2091 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e2091
          have b4e2349 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op y X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e73 (M.op X0 X1) X2
               have i₂ := b4e73 X1 X0
               grind)
            | (have i₁ := b4e73 (M.op y X0) X1
               have i₂ := b4e73 X0 y
               grind)
            | exact superpose b4e73 b4e73
            | exact resolve b4e73 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2350 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op y (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e73 (σ x) X0
               have i₂ := b4e48
               grind)
            | exact superpose b4e48 b4e73
            | exact resolve b4e73 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e2353 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e73 x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e73
            | exact resolve b4e73 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e4531 : ∀ X0 X1 : G, (M.op y (σ (M.op y (M.op X0 X1)))) = (M.op (σ (M.op y (M.op X0 X1))) (σ (M.op (M.op y (M.op X0 X1)) (M.op X0 (M.op y X1))))) := by
            intro X0 X1
            first
            | (have i₁ := b4e156 (M.op y (M.op X0 X1))
               have i₂ := b4e1142 X0 X1 (M.op y (M.op X0 X1))
               grind)
            | (have i₁ := b4e156 (M.op X0 (M.op y x))
               have i₂ := b4e1142 X0 x (M.op X0 (M.op y x))
               grind)
            | exact superpose b4e1142 b4e156
            | exact resolve b4e156 b4e1142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e156 b4e1142
          have b4e4623 : ∀ X0 X1 : G, (M.op y (σ (M.op y (M.op X0 X1)))) = (M.op y (σ (M.op (M.op y (M.op X0 X1)) (M.op X0 (M.op y X1))))) := by
            intro X0 X1
            first
            | (have i₁ := b4e4531 X0 X1
               have i₂ := b4e552 X0 X1 (σ (M.op (M.op y (M.op X0 X1)) (M.op X0 (M.op y X1))))
               grind)
            | exact superpose b4e552 b4e4531
            | exact resolve b4e4531 b4e552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e552 b4e4531
          have b4e4761 : ∀ X0 X1 : G, (M.op y (σ (M.op y (M.op X0 X1)))) = (M.op y (σ (M.op y (M.op (M.op y (M.op X0 X1)) (M.op X0 X1))))) := by
            intro X0 X1
            first
            | (have i₁ := b4e4623 X0 X1
               have i₂ := b4e2349 X0 X1 (M.op y (M.op X0 X1))
               grind)
            | exact superpose b4e2349 b4e4623
            | exact resolve b4e4623 b4e2349
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2349 b4e4623
          have b4e4848 : ∀ X0 X1 : G, (M.op y (σ (M.op y (M.op X0 X1)))) = (σ (M.op y (M.op (M.op y (M.op X0 X1)) (M.op X0 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e4761 X0 X1
               have i₂ := b4e2094 (M.op (M.op y (M.op X0 X1)) (M.op X0 X1))
               grind)
            | exact superpose b4e2094 b4e4761
            | exact resolve b4e4761 b4e2094
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4761
          have b4e4887 : ∀ X0 X1 : G, (σ (M.op y (M.op X0 (M.op y X1)))) = (M.op y (σ (M.op y (M.op X0 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e4848 X0 X1
               have i₂ := b4e86 X1 X0 y (M.op X0 X1)
               grind)
            | exact superpose b4e86 b4e4848
            | exact resolve b4e4848 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e86 b4e4848
          have b4e4907 : ∀ X0 X1 : G, (σ (M.op y (M.op X0 X1))) = (σ (M.op y (M.op X0 (M.op y X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e4887 X0 X1
               have i₂ := b4e2094 (M.op X0 X1)
               grind)
            | exact superpose b4e2094 b4e4887
            | exact resolve b4e4887 b4e2094
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2094 b4e4887
          have b4e4916 : ∀ X0 X1 : G, (σ (M.op y (M.op X0 X1))) = (σ (M.op X0 (M.op y X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e4907 X0 X1
               have i₂ := b4e1192 X0 X1
               grind)
            | (have i₁ := b4e4907 y X1
               have i₂ := b4e1192 y (M.op y X1)
               grind)
            | exact superpose b4e1192 b4e4907
            | exact resolve b4e4907 b4e1192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1192 b4e4907
          have b4e5253 : (M.op (σ x) (σ y)) = (M.op y (σ (M.op x x))) := by
            first
            | (have i₁ := b4e2350 (σ x)
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e2350
            | exact resolve b4e2350 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e2350
          have b4e5341 : (M.op (σ x) (σ y)) = (σ (M.op x (M.op y x))) := by
            first
            | (have i₁ := b4e5253
               have i₂ := b4e587 x
               grind)
            | exact superpose b4e587 b4e5253
            | exact resolve b4e5253 b4e587
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e587 b4e5253
          have b4e5361 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op x x))) := by
            first
            | (have i₁ := b4e5341
               have i₂ := b4e4916 x x
               grind)
            | exact superpose b4e4916 b4e5341
            | exact resolve b4e5341 b4e4916
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4916 b4e5341
          have b4e5367 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e5361
               have i₂ := b4e2353 x
               grind)
            | exact superpose b4e2353 b4e5361
            | exact resolve b4e5361 b4e2353
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2353 b4e5361
          have b4e5372 : False := by grind
          exact b4e5372
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
            intro X0 X1 X2 X3
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
          have b5e32 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e13 X3 (M.op X3 X2) X4 X5
               have i₂ := b5e13 X3 X2 X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) X1) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e13 (M.op X2 X3) X1 X4 X5
               have i₂ := b5e13 X0 X1 X2 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) X1) = (M.op (M.op X2 X3) (M.op y X1)) := by
            intro X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e33 x X1 X2 X3 X4 X5
               have i₂ := b5e36 x X1
               grind)
            | exact superpose b5e36 b5e33
            | exact resolve b5e33 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e42 : y = (M.op y y) := by
            first
            | (have i₁ := b5e36 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e36
            | exact resolve b5e36 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : ∀ X0 X1 : G, (M.op y (M.op X1 X0)) = (M.op X1 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e36 X1 (M.op X1 X0)
               have i₂ := b5e36 X1 X0
               grind)
            | exact superpose b5e36 b5e36
            | exact resolve b5e36 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48 : ∀ X0 X2 X3 : G, (M.op y X0) = (M.op (M.op X2 X3) X0) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e13 x X0 X2 X3
               have i₂ := b5e36 x X0
               grind)
            | exact superpose b5e36 b5e13
            | exact resolve b5e13 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e50 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op y X0)) = (M.op (M.op X2 X3) (M.op X1 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 (M.op X1 X0) X2 X3
               have i₂ := b5e36 X1 X0
               grind)
            | exact superpose b5e36 b5e13
            | exact resolve b5e13 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e58 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          clear b5e58
          have b5e65 : x = (k x y) := by
            first
            | (have r₁ := b5e62
               have r₂ := b5e21
               grind)
            | exact resolve b5e62 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b5e115 : ∀ X0 X1 : G, (M.op y X1) = (M.op (σ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e48 X1 (σ X0) (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e48
            | exact resolve b5e48 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e116 : ∀ X0 : G, (M.op y (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e36 (σ X0) (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e36
            | exact resolve b5e36 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e631 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 X5) (M.op X6 (M.op X0 X3))) = (M.op X6 (M.op X0 (M.op (M.op X1 X2) X3))) := by
            intro X0 X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b5e32 x x (M.op X0 X3) X6 X4 X5
               have i₂ := b5e32 X1 X2 X3 X0 x x
               grind)
            | (have i₁ := b5e32 X0 X1 (M.op (M.op X0 X1) X2) X3 X4 X5
               have i₂ := b5e32 X0 X1 X2 (M.op X0 X1) X4 X5
               grind)
            | exact superpose b5e32 b5e32
            | exact resolve b5e32 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e649 : ∀ X0 X1 X2 X3 X6 X7 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op X6 X7) (M.op y (M.op X0 X3))) := by
            intro X0 X1 X2 X3 X6 X7
            first
            | (have i₁ := b5e41 (M.op X0 X3) X6 X7 x x
               have i₂ := b5e32 X1 X2 X3 X0 x x
               grind)
            | (have i₁ := b5e41 (M.op (M.op X0 X1) X2) X2 X3 x x
               have i₂ := b5e32 X0 X1 X2 (M.op x x) x x
               grind)
            | exact superpose b5e32 b5e41
            | exact resolve b5e41 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e716 : ∀ X0 X1 X2 X3 X6 X7 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op y (M.op (M.op X6 X7) (M.op X0 X3))) := by
            intro X0 X1 X2 X3 X6 X7
            first
            | (have i₁ := b5e649 X0 X1 X2 X3 X6 X7
               have i₂ := b5e43 (M.op X0 X3) (M.op X6 X7)
               grind)
            | exact superpose b5e43 b5e649
            | exact resolve b5e649 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e649
          have b5e733 : ∀ X0 X3 X4 X5 X6 : G, (M.op (M.op X4 X5) (M.op X6 (M.op X0 X3))) = (M.op X6 (M.op X0 (M.op y X3))) := by
            intro X0 X3 X4 X5 X6
            first
            | (have i₁ := b5e631 X0 x x X3 X4 X5 X6
               have i₂ := b5e48 X3 x x
               grind)
            | exact superpose b5e48 b5e631
            | exact resolve b5e631 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e631
          have b5e788 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op y (M.op X0 (M.op y X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e716 X0 X1 X2 X3 x x
               have i₂ := b5e50 X3 X0 x x
               grind)
            | exact superpose b5e50 b5e716
            | exact resolve b5e716 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e716
          have b5e802 : ∀ X0 X3 X6 : G, (M.op X6 (M.op X0 (M.op y X3))) = (M.op X6 (M.op y (M.op X0 X3))) := by
            intro X0 X3 X6
            first
            | (have i₁ := b5e733 X0 X3 x x X6
               have i₂ := b5e50 (M.op X0 X3) X6 x x
               grind)
            | exact superpose b5e50 b5e733
            | exact resolve b5e733 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e733
          have b5e844 : ∀ X0 X3 : G, (M.op X0 (M.op y X3)) = (M.op y (M.op X0 (M.op y X3))) := by
            intro X0 X3
            first
            | (have i₁ := b5e788 X0 x x X3
               have i₂ := b5e48 X3 x x
               grind)
            | exact superpose b5e48 b5e788
            | exact resolve b5e788 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e788
          have b5e949 : ∀ X0 X1 X2 X3 : G, (M.op y X3) = (M.op (σ (M.op (M.op X0 X1) X2)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e115 (M.op y X2) X3
               have i₂ := b5e41 X2 y X2 X0 X1
               grind)
            | exact superpose b5e41 b5e115
            | exact resolve b5e115 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e954 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (σ (M.op y (M.op X0 X1))) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e115 (M.op X0 X1) X2
               have i₂ := b5e48 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b5e48 b5e115
            | exact resolve b5e115 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e958 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e115 y X0
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e115
            | exact resolve b5e115 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e966 : ∀ X0 : G, (M.op y (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e30 (M.op X0 X0)
               have i₂ := b5e115 X0 (σ (M.op X0 X0))
               grind)
            | exact superpose b5e115 b5e30
            | exact resolve b5e30 b5e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e115
          have b5e996 : ∀ X0 : G, (M.op y (σ (M.op X0 X0))) = (σ (M.op X0 (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b5e966 X0
               have i₂ := b5e50 X0 X0 X0 X0
               grind)
            | exact superpose b5e50 b5e966
            | exact resolve b5e966 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e966
          have b5e1008 : ∀ X2 X3 : G, (M.op y X3) = (M.op (σ (M.op y X2)) X3) := by
            intro X2 X3
            first
            | (have i₁ := b5e949 x x X2 X3
               have i₂ := b5e48 X2 x x
               grind)
            | exact superpose b5e48 b5e949
            | exact resolve b5e949 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e949
          have b5e1468 : (σ y) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e958 (σ x)
               grind)
            | exact superpose b5e958 b5e24
            | exact resolve b5e24 b5e958
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1469 : (σ (M.op y y)) = (M.op y (σ y)) := by
            first
            | (have i₁ := b5e30 y
               have i₂ := b5e958 (σ y)
               grind)
            | exact superpose b5e958 b5e30
            | exact resolve b5e30 b5e958
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e958
          have b5e1506 : (σ y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b5e1469
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e1469
            | exact resolve b5e1469 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1469
          have b5e1589 : ∀ X0 X1 : G, (M.op y (σ X1)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e36 (σ X0) (σ X1)
               have i₂ := b5e68 X0 X1
               grind)
            | exact superpose b5e68 b5e36
            | (have j1 := b5e68 X0 X1
               grind)
            | exact resolve b5e36 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1594 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op (σ (k X0 X1)) (M.op y X4)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e41 X4 (σ X0) (σ X1) X2 X3
               have i₂ := b5e68 X0 X1
               grind)
            | exact superpose b5e68 b5e41
            | (have j1 := b5e68 X0 X1
               grind)
            | exact resolve b5e41 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e68
          have b5e1641 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op y (M.op (σ (k X0 X1)) X4)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e1594 X0 X1 X2 X3 X4
               have i₂ := b5e43 X4 (σ (k X0 X1))
               grind)
            | exact superpose b5e43 b5e1594
            | (have j0 := b5e1594 X0 X1 X2 X3 X4
               grind)
            | exact resolve b5e1594 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1594
          have b5e1673 : ∀ X0 X1 X4 : G, (M.op y X4) = (M.op y (M.op (σ (k X0 X1)) X4)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X4
            first
            | (have i₁ := b5e1641 X0 X1 x x X4
               have i₂ := b5e48 X4 x x
               grind)
            | exact superpose b5e48 b5e1641
            | (have j0 := b5e1641 X0 X1 x x X4
               grind)
            | exact resolve b5e1641 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1641
          have b5e1699 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e43 x X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e43
            | exact resolve b5e43 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1701 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op y X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e43 (M.op X0 X1) X2
               have i₂ := b5e43 X1 X0
               grind)
            | (have i₁ := b5e43 (M.op y X0) X1
               have i₂ := b5e43 X0 y
               grind)
            | exact superpose b5e43 b5e43
            | exact resolve b5e43 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2991 : ∀ X0 : G, (σ (M.op (M.op y X0) (M.op y X0))) = (M.op y (σ (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b5e30 (M.op y X0)
               have i₂ := b5e1008 X0 (σ (M.op y X0))
               grind)
            | exact superpose b5e1008 b5e30
            | exact resolve b5e30 b5e1008
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1008
          have b5e3046 : ∀ X0 : G, (σ (M.op y (M.op (M.op y X0) X0))) = (M.op y (σ (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b5e2991 X0
               have i₂ := b5e43 X0 (M.op y X0)
               grind)
            | exact superpose b5e43 b5e2991
            | exact resolve b5e2991 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e2991
          have b5e3062 : ∀ X0 : G, (M.op y (σ (M.op y X0))) = (σ (M.op y (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b5e3046 X0
               have i₂ := b5e48 X0 y X0
               grind)
            | exact superpose b5e48 b5e3046
            | exact resolve b5e3046 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e3046
          have b5e3069 : ∀ X0 : G, (σ (M.op y X0)) = (M.op y (σ (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b5e3062 X0
               have i₂ := b5e36 y X0
               grind)
            | exact superpose b5e36 b5e3062
            | exact resolve b5e3062 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e3062
          have b5e3527 : ∀ X0 X1 : G, (M.op y (σ (M.op y (M.op X0 X1)))) = (M.op (σ (M.op y (M.op X0 X1))) (σ (M.op (M.op y (M.op X0 X1)) (M.op X0 (M.op y X1))))) := by
            intro X0 X1
            first
            | (have i₁ := b5e116 (M.op y (M.op X0 X1))
               have i₂ := b5e802 X0 X1 (M.op y (M.op X0 X1))
               grind)
            | (have i₁ := b5e116 (M.op X0 (M.op y x))
               have i₂ := b5e802 X0 x (M.op X0 (M.op y x))
               grind)
            | exact superpose b5e802 b5e116
            | exact resolve b5e116 b5e802
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e116 b5e802
          have b5e3604 : ∀ X0 X1 : G, (M.op y (σ (M.op y (M.op X0 X1)))) = (M.op y (σ (M.op (M.op y (M.op X0 X1)) (M.op X0 (M.op y X1))))) := by
            intro X0 X1
            first
            | (have i₁ := b5e3527 X0 X1
               have i₂ := b5e954 X0 X1 (σ (M.op (M.op y (M.op X0 X1)) (M.op X0 (M.op y X1))))
               grind)
            | exact superpose b5e954 b5e3527
            | exact resolve b5e3527 b5e954
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e954 b5e3527
          have b5e3730 : ∀ X0 X1 : G, (M.op y (σ (M.op y (M.op X0 X1)))) = (M.op y (σ (M.op y (M.op (M.op y (M.op X0 X1)) (M.op X0 X1))))) := by
            intro X0 X1
            first
            | (have i₁ := b5e3604 X0 X1
               have i₂ := b5e1701 X0 X1 (M.op y (M.op X0 X1))
               grind)
            | exact superpose b5e1701 b5e3604
            | exact resolve b5e3604 b5e1701
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1701 b5e3604
          have b5e3810 : ∀ X0 X1 : G, (M.op y (σ (M.op y (M.op X0 X1)))) = (σ (M.op y (M.op (M.op y (M.op X0 X1)) (M.op X0 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e3730 X0 X1
               have i₂ := b5e3069 (M.op (M.op y (M.op X0 X1)) (M.op X0 X1))
               grind)
            | exact superpose b5e3069 b5e3730
            | exact resolve b5e3730 b5e3069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3730
          have b5e3849 : ∀ X0 X1 : G, (σ (M.op y (M.op X0 (M.op y X1)))) = (M.op y (σ (M.op y (M.op X0 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e3810 X0 X1
               have i₂ := b5e50 X1 X0 y (M.op X0 X1)
               grind)
            | exact superpose b5e50 b5e3810
            | exact resolve b5e3810 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3810
          have b5e3869 : ∀ X0 X1 : G, (σ (M.op y (M.op X0 X1))) = (σ (M.op y (M.op X0 (M.op y X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e3849 X0 X1
               have i₂ := b5e3069 (M.op X0 X1)
               grind)
            | exact superpose b5e3069 b5e3849
            | exact resolve b5e3849 b5e3069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3069 b5e3849
          have b5e3878 : ∀ X0 X1 : G, (σ (M.op y (M.op X0 X1))) = (σ (M.op X0 (M.op y X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e3869 X0 X1
               have i₂ := b5e844 X0 X1
               grind)
            | (have i₁ := b5e3869 y X1
               have i₂ := b5e844 y (M.op y X1)
               grind)
            | exact superpose b5e844 b5e3869
            | exact resolve b5e3869 b5e844
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e844 b5e3869
          have b5e5740 : (M.op y (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e1589 x y
               have i₂ := b5e65
               grind)
            | exact superpose b5e65 b5e1589
            | (have j0 := b5e1589 x y
               grind)
            | exact resolve b5e1589 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1589
          have b5e5788 : (M.op y (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b5e5740
               have r₂ := b5e24
               grind)
            | exact resolve b5e5740 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5740
          have b5e5806 : (M.op y (σ y)) = (M.op (σ x) (σ x)) := by
            first
            | (have r₁ := b5e5788
               have r₂ := b5e23
               grind)
            | exact resolve b5e5788 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5788
          have b5e5818 : (M.op y (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e5806
               have i₂ := b5e30 x
               grind)
            | exact superpose b5e30 b5e5806
            | exact resolve b5e5806 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5806
          have b5e5825 : (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e5818
               have i₂ := b5e1506
               grind)
            | exact superpose b5e1506 b5e5818
            | exact resolve b5e5818 b5e1506
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1506 b5e5818
          have b5e5836 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x x) (M.op x x))) := by
            first
            | (have i₁ := b5e30 (M.op x x)
               have i₂ := b5e5825
               grind)
            | exact superpose b5e5825 b5e30
            | exact resolve b5e30 b5e5825
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5825
          have b5e5878 : (M.op (σ y) (σ y)) = (σ (M.op x (M.op y x))) := by
            first
            | (have i₁ := b5e5836
               have i₂ := b5e50 x x x x
               grind)
            | exact superpose b5e50 b5e5836
            | exact resolve b5e5836 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e5836
          have b5e5886 : (M.op (σ y) (σ y)) = (σ (M.op y (M.op x x))) := by
            first
            | (have i₁ := b5e5878
               have i₂ := b5e3878 x x
               grind)
            | exact superpose b5e3878 b5e5878
            | exact resolve b5e5878 b5e3878
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5878
          have b5e5891 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e5886
               have i₂ := b5e1699 x
               grind)
            | exact superpose b5e1699 b5e5886
            | exact resolve b5e5886 b5e1699
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5886
          have b5e5894 : (σ (M.op x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e5891
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e5891
            | exact resolve b5e5891 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5891
          have b5e5896 : (σ (M.op x y)) = (σ y) := by
            first
            | (have i₁ := b5e5894
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e5894
            | exact resolve b5e5894 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e5894
          have b5e6181 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e1673 x y X0
               have i₂ := b5e65
               grind)
            | exact superpose b5e65 b5e1673
            | (have j0 := b5e1673 x y x
               grind)
            | exact resolve b5e1673 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65 b5e1673
          have b5e6261 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op (σ x) X0)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b5e6181 X0
               grind)
            | (have r₁ := b5e6181 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e6181 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6181
          have b5e6275 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op (σ x) X0)) := by
            intro X0
            first
            | (have j0 := b5e6261 X0
               grind)
            | (have r₁ := b5e6261 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e6261 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6261
          have b5e7029 : (M.op y (σ x)) = (M.op y (σ (M.op x x))) := by
            first
            | (have i₁ := b5e6275 (σ x)
               have i₂ := b5e30 x
               grind)
            | exact superpose b5e30 b5e6275
            | exact resolve b5e6275 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e6275
          have b5e7110 : (M.op y (σ x)) = (σ (M.op x (M.op y x))) := by
            first
            | (have i₁ := b5e7029
               have i₂ := b5e996 x
               grind)
            | exact superpose b5e996 b5e7029
            | exact resolve b5e7029 b5e996
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e996 b5e7029
          have b5e7125 : (M.op y (σ x)) = (σ (M.op y (M.op x x))) := by
            first
            | (have i₁ := b5e7110
               have i₂ := b5e3878 x x
               grind)
            | exact superpose b5e3878 b5e7110
            | exact resolve b5e7110 b5e3878
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3878 b5e7110
          have b5e7132 : (σ (M.op x y)) = (M.op y (σ x)) := by
            first
            | (have i₁ := b5e7125
               have i₂ := b5e1699 x
               grind)
            | exact superpose b5e1699 b5e7125
            | exact resolve b5e7125 b5e1699
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1699 b5e7125
          have b5e7137 : (σ y) = (M.op y (σ x)) := by
            first
            | (have i₁ := b5e7132
               have i₂ := b5e5896
               grind)
            | exact superpose b5e5896 b5e7132
            | exact resolve b5e7132 b5e5896
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5896 b5e7132
          have b5e7141 : False := by grind
          exact b5e7141
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
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
            intro X0 X1 X2 X3
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
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
          have b7e33 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b7e13 X3 (M.op X3 X2) X4 X5
               have i₂ := b7e13 X3 X2 X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e51 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          clear b7e51
          have b7e56 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e54
               have r₂ := b7e23
               grind)
            | exact resolve b7e54 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
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
          have b7e71 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e61
               grind)
            | exact superpose b7e61 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e72 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e71
               have r₂ := b7e22
               grind)
            | exact resolve b7e71 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e74 : x = (M.op x y) := by
            first
            | (have r₁ := b7e72
               have r₂ := b7e21
               grind)
            | exact resolve b7e72 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e105 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e37 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e37
            | exact resolve b7e37 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e107 : (M.op x x) = (M.op (σ y) y) := by
            first
            | (have i₁ := b7e37 x y
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e37
            | exact resolve b7e37 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e110 : ∀ X0 X2 X3 : G, (M.op (σ y) X0) = (M.op (M.op X2 X3) X0) := by
            intro X0 X2 X3
            first
            | (have i₁ := b7e13 x X0 X2 X3
               have i₂ := b7e37 x X0
               grind)
            | exact superpose b7e37 b7e13
            | exact resolve b7e13 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e117 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e105
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e105
            | exact resolve b7e105 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e105
          have b7e204 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e117
               grind)
            | exact superpose b7e117 b7e14
            | exact resolve b7e14 b7e117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e117
          have b7e205 : y = (M.op y y) := by
            first
            | (have i₁ := b7e204
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e204
            | exact resolve b7e204 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e204
          have b7e355 : (M.op y y) = (M.op (σ y) y) := by
            first
            | (have i₁ := b7e37 y y
               have i₂ := b7e205
               grind)
            | exact superpose b7e205 b7e37
            | exact resolve b7e37 b7e205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e360 : y = (M.op (σ y) y) := by
            first
            | (have i₁ := b7e355
               have i₂ := b7e205
               grind)
            | exact superpose b7e205 b7e355
            | exact resolve b7e355 b7e205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e355
          have b7e654 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 X3) X1)) = (M.op y (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e33 X2 X3 X1 X0 y y
               have i₂ := b7e205
               grind)
            | exact superpose b7e205 b7e33
            | exact resolve b7e33 b7e205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e671 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op (M.op X2 X3) y)) = (M.op (M.op X0 X1) x) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e33 X2 X3 y x X0 X1
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e33
            | exact resolve b7e33 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e700 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op X2 (M.op x X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e33 x y X3 X2 X0 X1
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e33
            | exact resolve b7e33 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e701 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op X2 (M.op y X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e33 y y X3 X2 X0 X1
               have i₂ := b7e205
               grind)
            | exact superpose b7e205 b7e33
            | exact resolve b7e33 b7e205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e205
          have b7e810 : ∀ X2 X3 : G, (M.op (σ y) (M.op X2 X3)) = (M.op X2 (M.op y X3)) := by
            intro X2 X3
            first
            | (have i₁ := b7e701 x x X2 X3
               have i₂ := b7e110 (M.op X2 X3) x x
               grind)
            | exact superpose b7e110 b7e701
            | exact resolve b7e701 b7e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e701
          have b7e811 : ∀ X2 X3 : G, (M.op (σ y) (M.op X2 X3)) = (M.op X2 (M.op x X3)) := by
            intro X2 X3
            first
            | (have i₁ := b7e700 x x X2 X3
               have i₂ := b7e110 (M.op X2 X3) x x
               grind)
            | exact superpose b7e110 b7e700
            | exact resolve b7e700 b7e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e700
          have b7e826 : ∀ X2 X3 : G, (M.op (σ y) x) = (M.op x (M.op (M.op X2 X3) y)) := by
            intro X2 X3
            first
            | (have i₁ := b7e671 x x X2 X3
               have i₂ := b7e110 x x x
               grind)
            | exact superpose b7e110 b7e671
            | exact resolve b7e671 b7e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e671
          have b7e843 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op y (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e654 X0 X1 x x
               have i₂ := b7e110 X1 x x
               grind)
            | exact superpose b7e110 b7e654
            | exact resolve b7e654 b7e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e654
          have b7e888 : ∀ X2 X3 : G, (M.op X2 (M.op y X3)) = (M.op X2 (M.op x X3)) := by
            intro X2 X3
            first
            | (have i₁ := b7e811 X2 X3
               have i₂ := b7e810 X2 X3
               grind)
            | (have i₁ := b7e811 y X3
               have i₂ := b7e810 (σ y) X3
               grind)
            | exact superpose b7e810 b7e811
            | exact resolve b7e811 b7e810
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e810 b7e811
          have b7e897 : (M.op x (M.op (σ y) y)) = (M.op (σ y) x) := by
            first
            | (have i₁ := b7e826 x x
               have i₂ := b7e110 y x x
               grind)
            | exact superpose b7e110 b7e826
            | exact resolve b7e826 b7e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110 b7e826
          have b7e954 : (M.op (σ y) x) = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b7e897
               have i₂ := b7e843 x y
               grind)
            | exact superpose b7e843 b7e897
            | exact resolve b7e897 b7e843
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e843 b7e897
          have b7e1006 : (M.op (σ y) x) = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b7e954
               have i₂ := b7e888 y y
               grind)
            | exact superpose b7e888 b7e954
            | exact resolve b7e954 b7e888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e888 b7e954
          have b7e1045 : (M.op (σ y) y) = (M.op (σ y) x) := by
            first
            | (have i₁ := b7e1006
               have i₂ := b7e37 y y
               grind)
            | exact superpose b7e37 b7e1006
            | exact resolve b7e1006 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1006
          have b7e1074 : (M.op x x) = (M.op (σ y) x) := by
            first
            | (have i₁ := b7e1045
               have i₂ := b7e107
               grind)
            | exact superpose b7e107 b7e1045
            | exact resolve b7e1045 b7e107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1045
          have b7e2127 : y = (M.op x x) := by
            first
            | (have i₁ := b7e360
               have i₂ := b7e107
               grind)
            | exact superpose b7e107 b7e360
            | exact resolve b7e360 b7e107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e107 b7e360
          have b7e2353 : (M.op x y) = (M.op (σ y) x) := by
            first
            | (have i₁ := b7e37 x x
               have i₂ := b7e2127
               grind)
            | exact superpose b7e2127 b7e37
            | exact resolve b7e37 b7e2127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e2365 : x = (M.op (σ y) x) := by
            first
            | (have i₁ := b7e2353
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e2353
            | exact resolve b7e2353 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74 b7e2353
          have b7e2455 : x = (M.op x x) := by
            first
            | (have i₁ := b7e2365
               have i₂ := b7e1074
               grind)
            | exact superpose b7e1074 b7e2365
            | exact resolve b7e2365 b7e1074
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1074 b7e2365
          have b7e2482 : x = y := by
            first
            | (have i₁ := b7e2455
               have i₂ := b7e2127
               grind)
            | exact superpose b7e2127 b7e2455
            | exact resolve b7e2455 b7e2127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2127 b7e2455
          have b7e2490 : False := by grind
          exact b7e2490
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
          have b8e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e852 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e62 x y
               grind)
            | exact superpose b8e62 b8e20
            | (have j1 := b8e62 x y
               grind)
            | exact resolve b8e20 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e913 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e852
               have r₂ := b8e24
               grind)
            | exact resolve b8e852 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e852
          have b8e922 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e913
               have r₂ := b8e23
               grind)
            | exact resolve b8e913 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e913
          have b8e927 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e922
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e922
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e922
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e922
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e922 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e922
          have b8e928 : y = (M.op y x) ∨ x = y := by grind
          clear b8e927
          have b8e929 : x = y := by
            first
            | (have r₁ := b8e928
               have r₂ := b8e22
               grind)
            | exact resolve b8e928 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e928
          have b8e930 : False := by grind
          exact b8e930

/-- `Equation4434`: `x ◇ (y ◇ x) = (x ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation4434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4434.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 (M.op X0 X0) X3
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
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
      have b0e31 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
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
      have b0e37 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X1 x
           have i₂ := b0e11 X0 X2 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 : G, y = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e31 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e31
        | exact resolve b0e31 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e40 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e30 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e30
        | exact resolve b0e30 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e47 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
      have b0e49 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 y
           have i₂ := b0e39 y
           grind)
        | exact superpose b0e39 b0e14
        | (have j0 := b0e14 X0 y
           grind)
        | (have r₁ := b0e14 X0 y
           have r₂ := b0e39 y
           grind)
        | exact resolve b0e14 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
        intro X0
        first
        | (have j0 := b0e49 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49
      have b0e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
        intro X0
        first
        | (have j0 := b0e47 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e153 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 y
           have i₂ := b0e52 (σ X0)
           grind)
        | exact superpose b0e52 b0e17
        | exact resolve b0e17 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52
      have b0e157 : ∀ X0 : G, (k (σ X0) y) = (σ (k X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e153 X0
           have i₂ := b0e50 (σ X0)
           grind)
        | exact superpose b0e50 b0e153
        | exact resolve b0e153 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e153
      have b0e408 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op X3 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e37 X2 X3 (M.op X0 X0)
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e37
        | exact resolve b0e37 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e411 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e37 X0 X1 (σ y)
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e37
        | exact resolve b0e37 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e414 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e37 X0 X1 y
           have i₂ := b0e39 X0
           grind)
        | exact superpose b0e39 b0e37
        | exact resolve b0e37 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e39
      have b0e446 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e411 X0 x
           have i₂ := b0e414 X0 x
           grind)
        | exact superpose b0e414 b0e411
        | exact resolve b0e411 b0e414
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e411
      have b0e447 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op X2 y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e408 X0 X1 X2 x
           have i₂ := b0e414 X2 x
           grind)
        | exact superpose b0e414 b0e408
        | exact resolve b0e408 b0e414
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e408
      have b0e468 : ∀ X0 X2 : G, (M.op X2 y) = (M.op X2 (M.op X0 y)) := by
        intro X0 X2
        first
        | (have i₁ := b0e447 X0 x X2
           have i₂ := b0e414 X0 x
           grind)
        | exact superpose b0e414 b0e447
        | exact resolve b0e447 b0e414
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e447
      have b0e512 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e446 (σ x)
           grind)
        | exact superpose b0e446 b0e18
        | exact resolve b0e18 b0e446
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e446
      have b0e746 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) y) = (M.op X0 (M.op X1 (M.op X2 X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e50 (M.op X0 X0)
           have i₂ := b0e29 X1 X2 X0 (M.op X0 X0)
           grind)
        | exact superpose b0e29 b0e50
        | exact resolve b0e50 b0e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e789 : ∀ X0 X1 : G, (k (M.op X0 X0) y) = (M.op X0 (M.op X1 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e746 X0 X1 x
           have i₂ := b0e414 X1 x
           grind)
        | exact superpose b0e414 b0e746
        | exact resolve b0e746 b0e414
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e414 b0e746
      have b0e863 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 X0) y) := by
        intro X0
        first
        | (have i₁ := b0e789 X0 x
           have i₂ := b0e468 x X0
           grind)
        | exact superpose b0e468 b0e789
        | exact resolve b0e789 b0e468
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e468 b0e789
      have b0e2613 : ∀ X0 : G, (M.op X0 y) = (k (k X0 y) y) := by
        intro X0
        first
        | (have i₁ := b0e863 X0
           have i₂ := b0e50 X0
           grind)
        | exact superpose b0e50 b0e863
        | exact resolve b0e863 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50 b0e863
      have b0e5914 : ∀ X0 : G, (M.op (σ X0) y) = (k (σ (k X0 y)) y) := by
        intro X0
        first
        | (have i₁ := b0e2613 (σ X0)
           have i₂ := b0e157 X0
           grind)
        | exact superpose b0e157 b0e2613
        | exact resolve b0e2613 b0e157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e5925 : ∀ X0 : G, (M.op (σ X0) y) = (σ (k (k X0 y) y)) := by
        intro X0
        first
        | (have i₁ := b0e5914 X0
           have i₂ := b0e157 (k X0 y)
           grind)
        | exact superpose b0e157 b0e5914
        | exact resolve b0e5914 b0e157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e157 b0e5914
      have b0e5929 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e5925 X0
           have i₂ := b0e2613 X0
           grind)
        | exact superpose b0e2613 b0e5925
        | exact resolve b0e5925 b0e2613
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2613 b0e5925
      have b0e6922 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e512
           have i₂ := b0e5929 x
           grind)
        | exact superpose b0e5929 b0e512
        | (have r₁ := b0e512
           have r₂ := b0e5929 x
           grind)
        | exact resolve b0e512 b0e5929
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e512 b0e5929
      have b0e6927 : False := by grind
      exact b0e6927
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b1e29 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
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
        have b1e37 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e29 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e29
          | exact resolve b1e29 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e46 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b1e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e46 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e55 : (σ y) ≠ (k (σ y) y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e47 (σ y)
             grind)
          | exact superpose b1e47 b1e21
          | exact resolve b1e21 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b1e86 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) y) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e82 X0 X1
             have i₂ := b1e47 (σ X1)
             grind)
          | exact superpose b1e47 b1e82
          | (have j0 := b1e82 X0 X1
             grind)
          | exact resolve b1e82 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e82
        have b1e88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) y) ∨ (σ X1) = (k (σ X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b1e86 X0 X1
             have i₂ := b1e47 (σ X0)
             grind)
          | exact superpose b1e47 b1e86
          | (have j0 := b1e86 X0 X1
             grind)
          | exact resolve b1e86 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e86
        have b1e8473 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e88 y y
             grind)
          | exact superpose b1e88 b1e21
          | (have j1 := b1e88 y y
             grind)
          | exact resolve b1e21 b1e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e88
        have b1e8569 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) := by grind
        clear b1e8473
        have b1e8625 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b1e8569
             have r₂ := b1e55
             grind)
          | exact resolve b1e8569 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e8569
        have b1e8660 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e8625
             have i₂ := b1e47 y
             grind)
          | exact superpose b1e47 b1e8625
          | exact resolve b1e8625 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47 b1e8625
        have b1e8672 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e8660
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e8660
          | exact resolve b1e8660 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8660
        have b1e8673 : False := by grind
        exact b1e8673
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b2e26 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
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
        have b2e35 : ∀ X0 : G, y = (M.op y X0) := by
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
        have b2e42 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b2e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b2e42 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42
        have b2e51 : (σ y) ≠ (k (σ y) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e44 (σ y)
             grind)
          | exact superpose b2e44 b2e21
          | exact resolve b2e21 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b2e80 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) y) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e76 X0 X1
             have i₂ := b2e44 (σ X1)
             grind)
          | exact superpose b2e44 b2e76
          | (have j0 := b2e76 X0 X1
             grind)
          | exact resolve b2e76 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76
        have b2e82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) y) ∨ (σ X1) = (k (σ X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b2e80 X0 X1
             have i₂ := b2e44 (σ X0)
             grind)
          | exact superpose b2e44 b2e80
          | (have j0 := b2e80 X0 X1
             grind)
          | exact resolve b2e80 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e80
        have b2e8585 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e82 y y
             grind)
          | exact superpose b2e82 b2e21
          | (have j1 := b2e82 y y
             grind)
          | exact resolve b2e21 b2e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e8671 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) := by grind
        clear b2e8585
        have b2e8721 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b2e8671
             have r₂ := b2e51
             grind)
          | exact resolve b2e8671 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e8671
        have b2e8746 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e8721
             have i₂ := b2e44 y
             grind)
          | exact superpose b2e44 b2e8721
          | exact resolve b2e8721 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44 b2e8721
        have b2e8753 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e8746
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e8746
          | exact resolve b2e8746 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8746
        have b2e8754 : False := by grind
        exact b2e8754
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
        have b3e28 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
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
        have b3e37 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
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
        have b3e41 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X0) ∨ (M.op X2 X2) = (k X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e15 X2 (M.op X0 X0)
             have i₂ := b3e12 X0 X1 (M.op X0 X0)
             grind)
          | exact superpose b3e12 b3e15
          | (have j0 := b3e15 X2 (M.op X0 X0)
             grind)
          | exact resolve b3e15 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e114 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0 X1
          grind
        have b3e122 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b3e114 X0 x
             have j1 := b3e41 X0 x X0
             grind)
          | (have r₁ := b3e114 X0 x
             have r₂ := b3e41 X0 x x
             grind)
          | exact resolve b3e114 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41 b3e114
        have b3e185 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e122 (σ y)
             have i₂ := b3e37 (σ y)
             grind)
          | exact superpose b3e37 b3e122
          | exact resolve b3e122 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37 b3e122
        have b3e189 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e185
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e185
          | exact resolve b3e185 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e185
        have b3e194 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e189
             grind)
          | exact superpose b3e189 b3e13
          | exact resolve b3e13 b3e189
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e189
        have b3e196 : y = (k y y) := by
          first
          | (have i₁ := b3e194
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e194
          | exact resolve b3e194 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e194
        have b3e208 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e196
             grind)
          | exact superpose b3e196 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e196
        have b3e209 : y = (M.op y y) := by grind
        clear b3e208
        have b3e211 : False := by grind
        exact b3e211
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
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
          have b4e21 : y ≠ (M.op y y) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e34 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
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
          have b4e35 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
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
          have b4e43 : ∀ X0 X1 : G, (M.op y X0) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e35 X1
               have i₂ := b4e35 X0
               grind)
            | exact superpose b4e35 b4e35
            | exact resolve b4e35 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X0) ∨ (M.op X2 X2) = (k X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X2 (M.op X0 X0)
               have i₂ := b4e13 X0 X1 (M.op X0 X0)
               grind)
            | exact superpose b4e13 b4e16
            | (have j0 := b4e16 X2 (M.op X0 X0)
               grind)
            | exact resolve b4e16 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e66 : ∀ X0 X1 X2 : G, (M.op y (M.op X1 y)) = (M.op (M.op y X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 y X1 X2
               have i₂ := b4e43 y X0
               grind)
            | (have i₁ := b4e13 y X1 X2
               have i₂ := b4e43 X0 y
               grind)
            | exact superpose b4e43 b4e13
            | exact resolve b4e13 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e67 : ∀ X0 X2 : G, (M.op x y) = (M.op (M.op y X0) X2) := by
            intro X0 X2
            first
            | (have i₁ := b4e66 X0 x X2
               have i₂ := b4e35 (M.op x y)
               grind)
            | exact superpose b4e35 b4e66
            | exact resolve b4e66 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66
          have b4e77 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X2 X2) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X1 X2
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X2 X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e18 (σ X0) (σ X1)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X1) (σ X1)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e204 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e20
               have i₂ := b4e34 X0
               grind)
            | exact superpose b4e34 b4e20
            | exact resolve b4e20 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e490 : ∀ X0 X1 : G, (M.op (σ y) X1) ≠ (σ (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e204 X1
               have i₂ := b4e35 X0
               grind)
            | exact superpose b4e35 b4e204
            | exact resolve b4e204 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e204
          have b4e895 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op y X0) ∨ (M.op X1 X1) = (k X1 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 (M.op y X0)
               have i₂ := b4e67 X0 (M.op y X0)
               grind)
            | exact superpose b4e67 b4e16
            | (have j0 := b4e16 X1 (M.op y X0)
               grind)
            | exact resolve b4e16 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67
          have b4e920 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op y X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e895 X0 X1
               grind)
            | (have r₁ := b4e895 X0 X1
               have r₂ := b4e35 X0
               grind)
            | exact resolve b4e895 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35 b4e895
          have b4e2118 : ∀ X1 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op X1 X1) = (k X1 (M.op (σ y) (σ y))) := by
            intro X1
            first
            | (have i₁ := b4e46 (σ y) x X1
               have i₂ := b4e34 (M.op x (σ y))
               grind)
            | exact superpose b4e34 b4e46
            | (have j0 := b4e46 (σ y) X1 X1
               grind)
            | exact resolve b4e46 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e2132 : ∀ X1 : G, (M.op X1 X1) = (k X1 (M.op (σ y) (σ y))) := by
            intro X1
            first
            | (have j0 := b4e2118 X1
               grind)
            | (have r₁ := b4e2118 X1
               have r₂ := b4e34 (σ y)
               grind)
            | exact resolve b4e2118 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e2118
          have b4e3658 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e77 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77
          have b4e3660 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e3658 X0 X1
               have j1 := b4e16 X0 X0
               grind)
            | (have r₁ := b4e3658 X1 X1
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e3658 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3658
          have b4e7683 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e89 x x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e89
            | exact resolve b4e89 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e8001 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
          clear b4e7683
          have b4e12268 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (k y y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e2132 X0
               have i₂ := b4e89 y y
               grind)
            | exact superpose b4e89 b4e2132
            | (have j1 := b4e89 y y
               grind)
            | exact resolve b4e2132 b4e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89 b4e2132
          have b4e12404 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (k y y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have j0 := b4e12268 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12268
          have b4e12480 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (k y y))) := by
            intro X0
            first
            | (have j0 := b4e12404 X0
               grind)
            | (have r₁ := b4e12404 X0
               have r₂ := b4e23
               grind)
            | exact resolve b4e12404 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12404
          have b4e12641 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op y y))) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b4e12480 X0
               have i₂ := b4e18 y y
               grind)
            | exact superpose b4e18 b4e12480
            | (have j1 := b4e18 y y
               grind)
            | exact resolve b4e12480 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12480
          have b4e12765 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op y y))) ∨ y = (M.op y y) := by
            intro X0
            first
            | (have j0 := b4e12641 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12641
          have b4e12851 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op y y))) := by
            intro X0
            first
            | (have j0 := b4e12765 X0
               grind)
            | (have r₁ := b4e12765 X0
               have r₂ := b4e21
               grind)
            | exact resolve b4e12765 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12765
          have b4e13041 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op y X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e12851 X1
               have i₂ := b4e43 y X0
               grind)
            | (have i₁ := b4e12851 X1
               have i₂ := b4e43 X0 y
               grind)
            | exact superpose b4e43 b4e12851
            | exact resolve b4e12851 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43 b4e12851
          have b4e13400 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b4e3660 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e3660
            | exact resolve b4e3660 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3660
          have b4e13475 : (σ y) = (σ (k x x)) ∨ (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b4e13400
               have i₂ := b4e19 x x
               grind)
            | exact superpose b4e19 b4e13400
            | exact resolve b4e13400 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13400
          have b4e13497 : (σ y) = (σ (k x x)) := by
            first
            | (have r₁ := b4e13475
               have r₂ := b4e8001
               grind)
            | exact resolve b4e13475 b4e8001
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8001 b4e13475
          have b4e13516 : (k x x) = (τ (σ y)) := by
            first
            | (have i₁ := b4e14 (k x x)
               have i₂ := b4e13497
               grind)
            | exact superpose b4e13497 b4e14
            | exact resolve b4e14 b4e13497
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e13517 : ∀ X0 : G, (σ (k (k x x) X0)) = (k (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 (k x x) X0
               have i₂ := b4e13497
               grind)
            | exact superpose b4e13497 b4e19
            | exact resolve b4e19 b4e13497
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13497
          have b4e13531 : ∀ X0 : G, (σ (k y X0)) = (σ (k (k x x) X0)) := by
            intro X0
            first
            | (have i₁ := b4e13517 X0
               have i₂ := b4e19 y X0
               grind)
            | exact superpose b4e19 b4e13517
            | exact resolve b4e13517 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13517
          have b4e13532 : y = (k x x) := by
            first
            | (have i₁ := b4e13516
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e13516
            | exact resolve b4e13516 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13516
          have b4e17813 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (M.op y X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 (M.op y X1)
               have i₂ := b4e13041 X1 (σ X0)
               grind)
            | exact superpose b4e13041 b4e19
            | exact resolve b4e19 b4e13041
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13041
          have b4e50702 : ∀ X0 : G, (σ (M.op (k x x) (k x x))) = (σ (k y (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b4e13531 (M.op y X0)
               have i₂ := b4e920 X0 (k x x)
               grind)
            | exact superpose b4e920 b4e13531
            | exact resolve b4e13531 b4e920
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e920 b4e13531
          have b4e50770 : (M.op (σ y) (σ y)) = (σ (M.op (k x x) (k x x))) := by
            first
            | (have i₁ := b4e50702 x
               have i₂ := b4e17813 y x
               grind)
            | exact superpose b4e17813 b4e50702
            | exact resolve b4e50702 b4e17813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17813 b4e50702
          have b4e50812 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e50770
               have i₂ := b4e13532
               grind)
            | exact superpose b4e13532 b4e50770
            | exact resolve b4e50770 b4e13532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13532 b4e50770
          have b4e50841 : False := by grind
          exact b4e50841
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e32 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e13 x x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e13 X0 x X3
               have i₂ := b5e13 X0 x X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 : G, (M.op y X0) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e32 X1
               have i₂ := b5e32 X0
               grind)
            | exact superpose b5e32 b5e32
            | exact resolve b5e32 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : ∀ X1 : G, (M.op x y) = (M.op (M.op y y) X1) := by
            intro X1
            first
            | (have i₁ := b5e13 y x X1
               have i₂ := b5e32 (M.op x y)
               grind)
            | exact superpose b5e32 b5e13
            | exact resolve b5e13 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e59 : ∀ X0 : G, y ≠ (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e21
               have i₂ := b5e41 y X0
               grind)
            | (have i₁ := b5e21
               have i₂ := b5e41 X0 y
               grind)
            | exact superpose b5e41 b5e21
            | exact resolve b5e21 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e72 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X2 X2) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X1 X2
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X2 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e78 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X0 X2
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X1 X0)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X0 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b5e164 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (M.op x y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 (M.op y y) X1
               have i₂ := b5e43 X0
               grind)
            | exact superpose b5e43 b5e13
            | exact resolve b5e13 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e282 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X0 X0) X2 X3
               have i₂ := b5e35 X0 (M.op X0 X0) X1
               grind)
            | (have i₁ := b5e13 (M.op X0 X0) X2 X3
               have i₂ := b5e35 X0 X1 (M.op X0 X0)
               grind)
            | exact superpose b5e35 b5e13
            | exact resolve b5e13 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e301 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X0 X0))) = (M.op (M.op X0 (M.op x y)) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e282 X0 x X2 X3
               have i₂ := b5e164 X0 x
               grind)
            | exact superpose b5e164 b5e282
            | exact resolve b5e282 b5e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e282
          have b5e327 : ∀ X0 X3 : G, (M.op X0 (M.op x y)) = (M.op (M.op X0 (M.op x y)) X3) := by
            intro X0 X3
            first
            | (have i₁ := b5e301 X0 x X3
               have i₂ := b5e164 X0 (M.op x (M.op X0 X0))
               grind)
            | exact superpose b5e164 b5e301
            | exact resolve b5e301 b5e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e164 b5e301
          have b5e3019 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e72 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72
          have b5e3021 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e3019 X0 X1
               have j1 := b5e16 X0 X0
               grind)
            | (have r₁ := b5e3019 X1 X1
               have r₂ := b5e16 X0 X1
               grind)
            | exact resolve b5e3019 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3019
          have b5e3283 : ∀ X0 : G, y = (k x x) ∨ y = (M.op x X0) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b5e78 x x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e78
            | exact resolve b5e78 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e7012 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e84 x x
               grind)
            | exact superpose b5e84 b5e24
            | (have j1 := b5e84 x x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e84 x y
               grind)
            | exact resolve b5e24 b5e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84
          have b5e7196 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e7012
          have b5e10414 : x ≠ y ∨ y = (k x x) := by
            first
            | (have i₁ := b5e3021 x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e3021
            | exact resolve b5e3021 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e18024 : ∀ X0 : G, y = (M.op y X0) ∨ y = (k x x) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b5e327 x x
               have i₂ := b5e3283 (M.op x y)
               grind)
            | exact superpose b5e3283 b5e327
            | exact resolve b5e327 b5e3283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e327 b5e3283
          have b5e18038 : ∀ X0 : G, y = (M.op y X0) ∨ y = (k x x) := by
            intro X0
            first
            | (have j0 := b5e18024 X0
               grind)
            | (have r₁ := b5e18024 X0
               have r₂ := b5e10414
               grind)
            | exact resolve b5e18024 b5e10414
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10414 b5e18024
          have b5e18130 : y = (k x x) := by
            first
            | (have r₁ := b5e18038 x
               have r₂ := b5e59 x
               grind)
            | exact resolve b5e18038 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59 b5e18038
          have b5e33716 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e7196
               have i₂ := b5e18130
               grind)
            | exact superpose b5e18130 b5e7196
            | exact resolve b5e7196 b5e18130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7196
          have b5e33729 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e33716
          have b5e33758 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e33729
               grind)
            | exact superpose b5e33729 b5e24
            | exact resolve b5e24 b5e33729
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33821 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b5e3021 (σ x) (σ x)
               have i₂ := b5e33729
               grind)
            | exact superpose b5e33729 b5e3021
            | (have r₁ := b5e3021 (σ x) (σ x)
               have r₂ := b5e33729
               grind)
            | exact resolve b5e3021 b5e33729
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3021 b5e33729
          have b5e33822 : (σ x) = (k (σ x) (σ x)) := by grind
          clear b5e33821
          have b5e33825 : (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b5e33822
               have i₂ := b5e19 x x
               grind)
            | exact superpose b5e19 b5e33822
            | exact resolve b5e33822 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33822
          have b5e33861 : (σ x) = (σ y) := by
            first
            | (have i₁ := b5e33825
               have i₂ := b5e18130
               grind)
            | exact superpose b5e18130 b5e33825
            | exact resolve b5e33825 b5e18130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e18130 b5e33825
          have b5e33872 : False := by grind
          exact b5e33872
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
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
        have b6e26 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
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
        have b6e35 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
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
        have b6e43 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e15 X0 (σ y)
             have i₂ := b6e35 (σ y)
             grind)
          | exact superpose b6e35 b6e15
          | (have j0 := b6e15 X0 (σ y)
             grind)
          | (have r₁ := b6e15 X0 (σ y)
             have r₂ := b6e35 (σ y)
             grind)
          | exact resolve b6e15 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e43 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e50 : ∀ X0 X1 : G, (k X0 (σ y)) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e45 X0
             grind)
          | exact superpose b6e45 b6e15
          | (have j0 := b6e15 X1 X0
             grind)
          | exact resolve b6e15 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e109 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (σ y)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          grind
        clear b6e45
        have b6e114 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b6e109 X0
             have j1 := b6e50 (M.op X0 X0) X0
             grind)
          | (have r₁ := b6e109 X0
             have r₂ := b6e50 (M.op X0 X0) x
             grind)
          | exact resolve b6e109 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50 b6e109
        have b6e124 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e114 (σ y)
             have i₂ := b6e35 (σ y)
             grind)
          | exact superpose b6e35 b6e114
          | exact resolve b6e114 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35 b6e114
        have b6e132 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e124
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e124
          | exact resolve b6e124 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e124
        have b6e146 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e132
             grind)
          | exact superpose b6e132 b6e13
          | exact resolve b6e13 b6e132
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e132
        have b6e148 : y = (k y y) := by
          first
          | (have i₁ := b6e146
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e146
          | exact resolve b6e146 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e146
        have b6e242 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e148
             grind)
          | exact superpose b6e148 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e148
        have b6e243 : y = (M.op y y) := by grind
        clear b6e242
        have b6e245 : False := by grind
        exact b6e245
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
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
          have b7e66 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X2 X2) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
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
          have b7e72 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X0 X0 X2
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e18 X0 (M.op X1 X0)
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X0 X0
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b7e113 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          have b7e135 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e113
               have r₂ := b7e23
               grind)
            | exact resolve b7e113 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e113
          have b7e136 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e135
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e135
            | exact resolve b7e135 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e135
          have b7e140 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e136
               grind)
            | exact superpose b7e136 b7e14
            | exact resolve b7e14 b7e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e136
          have b7e141 : y = (k x y) := by
            first
            | (have i₁ := b7e140
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e140
            | exact resolve b7e140 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e140
          have b7e156 : y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e141
               grind)
            | exact superpose b7e141 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e141
          have b7e157 : y = (M.op x y) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e156
               have r₂ := b7e21
               grind)
            | exact resolve b7e156 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e156
          have b7e159 : y = (M.op x y) := by
            first
            | (have r₁ := b7e157
               have r₂ := b7e22
               grind)
            | exact resolve b7e157 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e157
          have b7e2605 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e66 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e2607 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e2605 X0 X1
               have j1 := b7e16 X0 X0
               grind)
            | (have r₁ := b7e2605 X1 X1
               have r₂ := b7e16 X0 X1
               grind)
            | exact resolve b7e2605 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2605
          have b7e2952 : ∀ X0 : G, y ≠ (M.op x X0) ∨ x = (M.op x x) ∨ (M.op x x) = (k x x) := by
            intro X0
            first
            | (have i₁ := b7e22
               have i₂ := b7e72 x x X0
               grind)
            | (have i₁ := b7e22
               have i₂ := b7e72 x x x
               grind)
            | exact superpose b7e72 b7e22
            | (have j1 := b7e72 x x x
               grind)
            | exact resolve b7e22 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e3170 : ∀ X0 : G, y ≠ (M.op x X0) ∨ (M.op x x) = (k x x) := by
            intro X0
            first
            | (have j0 := b7e2952 X0
               have j1 := b7e16 x x
               grind)
            | (have r₁ := b7e2952 X0
               have r₂ := b7e16 X0 x
               grind)
            | exact resolve b7e2952 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2952
          have b7e6993 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e78 x x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e78
            | exact resolve b7e78 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e7353 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
          clear b7e6993
          have b7e10580 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b7e2607 (σ x) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e2607
            | exact resolve b7e2607 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2607
          have b7e10620 : (σ y) = (σ (k x x)) ∨ (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e10580
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e10580
            | exact resolve b7e10580 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10580
          have b7e10642 : (σ y) = (σ (k x x)) := by
            first
            | (have r₁ := b7e10620
               have r₂ := b7e7353
               grind)
            | exact resolve b7e10620 b7e7353
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7353 b7e10620
          have b7e10661 : (τ (σ y)) = (k x x) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e10642
               grind)
            | exact superpose b7e10642 b7e14
            | exact resolve b7e14 b7e10642
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10642
          have b7e10677 : y = (k x x) := by
            first
            | (have i₁ := b7e10661
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e10661
            | exact resolve b7e10661 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10661
          have b7e10679 : y ≠ y ∨ (M.op x x) = (k x x) := by
            first
            | (have i₁ := b7e3170 y
               have i₂ := b7e159
               grind)
            | exact superpose b7e159 b7e3170
            | (have r₁ := b7e3170 y
               have r₂ := b7e159
               grind)
            | exact resolve b7e3170 b7e159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e159 b7e3170
          have b7e10698 : (M.op x x) = (k x x) := by grind
          clear b7e10679
          have b7e10707 : y = (M.op x x) := by
            first
            | (have i₁ := b7e10698
               have i₂ := b7e10677
               grind)
            | exact superpose b7e10677 b7e10698
            | exact resolve b7e10698 b7e10677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10677 b7e10698
          have b7e10714 : False := by grind
          exact b7e10714
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
          have b8e1438 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e73 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e1439 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1438
               have r₂ := b8e23
               grind)
            | exact resolve b8e1438 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1438
          have b8e1440 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1439
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1439
            | exact resolve b8e1439 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1439
          have b8e1441 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1440
               grind)
            | exact superpose b8e1440 b8e20
            | exact resolve b8e20 b8e1440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1440
          have b8e1562 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e1441
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1441
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e1441 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1441
          have b8e1563 : y = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e1562
          have b8e1565 : y = (M.op x x) := by
            first
            | (have r₁ := b8e1563
               have r₂ := b8e21
               grind)
            | exact resolve b8e1563 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1563
          have b8e1567 : False := by grind
          exact b8e1567

/-- `Equation4434`: `x ◇ (y ◇ x) = (x ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxy_pxx_pxy_Equation4434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
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
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
      have b0e64 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e67 : False := by grind
      exact b0e67
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b4e34 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X1 x
               have i₂ := b4e13 X0 X2 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x x)) X0) := by
            intro X0
            first
            | (have i₁ := b4e34 X0
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e34
            | exact resolve b4e34 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e149 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e38 x X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e38
            | exact resolve b4e38 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e184 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x x) (M.op x x))) := by
            first
            | (have i₁ := b4e30 (M.op x x)
               have i₂ := b4e40 (σ (M.op x x))
               grind)
            | exact superpose b4e40 b4e30
            | exact resolve b4e30 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30
          have b4e190 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (M.op (σ x) (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (σ (M.op x x)) X1
               have i₂ := b4e40 X0
               grind)
            | exact superpose b4e40 b4e13
            | exact resolve b4e13 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e194 : (M.op x y) = (M.op x (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b4e149 (σ (M.op x x))
               have i₂ := b4e40 x
               grind)
            | exact superpose b4e40 b4e149
            | exact resolve b4e149 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e149
          have b4e197 : (M.op (σ x) (σ y)) = (σ (M.op x (M.op (σ x) (σ y)))) := by
            first
            | (have i₁ := b4e184
               have i₂ := b4e190 x (M.op x x)
               grind)
            | exact superpose b4e190 b4e184
            | exact resolve b4e184 b4e190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e184 b4e190
          have b4e201 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e197
               have i₂ := b4e194
               grind)
            | exact superpose b4e194 b4e197
            | exact resolve b4e197 b4e194
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e194 b4e197
          have b4e204 : False := by grind
          exact b4e204
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
          have b5e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op X0 X0) X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e13 X0 x X3
               have i₂ := b5e13 X0 x X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X1 x
               have i₂ := b5e13 X0 X2 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X2 (M.op x (M.op X0 X0))
               have i₂ := b5e13 (M.op X0 X0) x X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b5e93 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34 (σ X0) X1 x
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e34
            | exact resolve b5e34 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e105 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op X0 X0) X3
               have i₂ := b5e34 X0 X2 X1
               grind)
            | (have i₁ := b5e13 X2 (M.op X0 X0) X3
               have i₂ := b5e34 X0 X1 X2
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e140 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e37 x X0 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e37
            | exact resolve b5e37 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e167 : ∀ X1 : G, (M.op x y) = (M.op (M.op x x) X1) := by
            intro X1
            first
            | (have i₁ := b5e13 x x X1
               have i₂ := b5e140 x
               grind)
            | exact superpose b5e140 b5e13
            | exact resolve b5e13 b5e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e203 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (M.op x y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 x x X0 X1
               have i₂ := b5e140 x
               grind)
            | exact superpose b5e140 b5e33
            | exact resolve b5e33 b5e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e140
          have b5e267 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (M.op X2 (M.op x y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33 X2 (M.op x x) X0 X1
               have i₂ := b5e167 X2
               grind)
            | exact superpose b5e167 b5e33
            | exact resolve b5e33 b5e167
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33 b5e167
          have b5e280 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X2 (M.op x y))) := by
            intro X0 X2
            first
            | (have i₁ := b5e267 X0 x X2
               have i₂ := b5e203 X0 x
               grind)
            | exact superpose b5e203 b5e267
            | exact resolve b5e267 b5e203
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e267
          have b5e315 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op (M.op X0 X0) X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e38 X0 X3 X2
               have i₂ := b5e34 X0 (M.op X0 X0) X1
               grind)
            | (have i₁ := b5e38 X0 X3 X2
               have i₂ := b5e34 X0 X1 (M.op X0 X0)
               grind)
            | exact superpose b5e34 b5e38
            | exact resolve b5e38 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e38
          have b5e379 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op X0 (M.op x y)) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e315 X0 x X2 X3
               have i₂ := b5e203 X0 x
               grind)
            | exact superpose b5e203 b5e315
            | exact resolve b5e315 b5e203
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e315
          have b5e1128 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X1) (σ X0)
               have i₂ := b5e53 X1 X0
               grind)
            | exact superpose b5e53 b5e17
            | (have j0 := b5e17 (σ X0) (σ X1)
               have j1 := b5e53 X1 X0
               grind)
            | (have r₁ := b5e17 (σ X0) (σ X1)
               have r₂ := b5e53 X0 X1
               grind)
            | exact resolve b5e17 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e1137 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e1128 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1128
          have b5e1138 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e1137 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1137
          have b5e1148 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e1138 X0 X1
               have i₂ := b5e30 X1
               grind)
            | exact superpose b5e30 b5e1138
            | (have j0 := b5e1138 X0 X1
               grind)
            | exact resolve b5e1138 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1138
          have b5e1170 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e1148 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e1148
            | (have j0 := b5e1148 X0 X1
               grind)
            | exact resolve b5e1148 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1148
          have b5e1334 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e30 (M.op X0 X0)
               have i₂ := b5e93 X0 (σ (M.op X0 X0)) X1
               grind)
            | (have i₁ := b5e30 (M.op X0 X0)
               have i₂ := b5e93 X0 X1 (σ (M.op X0 X0))
               grind)
            | exact superpose b5e93 b5e30
            | exact resolve b5e30 b5e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1379 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (σ (M.op X0 (M.op x y))) := by
            intro X0 X1
            first
            | (have i₁ := b5e1334 X0 X1
               have i₂ := b5e203 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e203 b5e1334
            | exact resolve b5e1334 b5e203
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1334
          have b5e1532 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ X0) (M.op (M.op X2 X2) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e105 X2 X3 (σ X0) X1
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e105
            | exact resolve b5e105 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e105
          have b5e1769 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ X0) (M.op X2 (M.op x y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1532 X0 X1 X2 x
               have i₂ := b5e203 X2 x
               grind)
            | exact superpose b5e203 b5e1532
            | exact resolve b5e1532 b5e203
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e203 b5e1532
          have b5e1846 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ X0) (M.op x y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e1769 X0 X1 x
               have i₂ := b5e280 (σ X0) x
               grind)
            | exact superpose b5e280 b5e1769
            | exact resolve b5e1769 b5e280
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e280 b5e1769
          have b5e6367 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (τ (M.op (σ (M.op X0 X0)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (M.op X0 (M.op x y))
               have i₂ := b5e1379 X0 X1
               grind)
            | exact superpose b5e1379 b5e14
            | exact resolve b5e14 b5e1379
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1379
          have b5e6390 : ∀ X0 : G, (M.op X0 (M.op x y)) = (τ (M.op (σ X0) (M.op x y))) := by
            intro X0
            first
            | (have i₁ := b5e6367 X0 x
               have i₂ := b5e1846 X0 x
               grind)
            | exact superpose b5e1846 b5e6367
            | exact resolve b5e6367 b5e1846
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1846 b5e6367
          have b5e39570 : (σ y) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1170 x y
               grind)
            | exact superpose b5e1170 b5e24
            | (have j1 := b5e1170 x y
               grind)
            | exact resolve b5e24 b5e1170
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1170
          have b5e39826 : (σ y) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b5e39570
               have r₂ := b5e23
               grind)
            | exact resolve b5e39570 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39570
          have b5e65732 : (σ y) ≠ (σ (M.op y x)) ∨ (σ (M.op y y)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b5e39826
               have i₂ := b5e18 y x
               grind)
            | exact superpose b5e18 b5e39826
            | (have j1 := b5e18 y x
               grind)
            | (have r₁ := b5e39826
               have r₂ := b5e18 (σ y) (σ (k y x))
               grind)
            | (have r₁ := b5e39826
               have r₂ := b5e18 (σ (k y x)) (σ y)
               grind)
            | exact resolve b5e39826 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39826
          have b5e65733 : (σ y) ≠ (σ (M.op y x)) ∨ (σ (M.op y y)) = (σ (M.op y x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b5e65732
               have r₂ := b5e21
               grind)
            | exact resolve b5e65732 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65732
          have b5e65734 : (σ y) ≠ (σ y) ∨ (σ (M.op y y)) = (σ (M.op y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e65733
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e65733
            | exact resolve b5e65733 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65733
          have b5e65735 : (σ (M.op y y)) = (σ (M.op y x)) ∨ x = (M.op x y) := by grind
          clear b5e65734
          have b5e65736 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e65735
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e65735
            | exact resolve b5e65735 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65735
          have b5e65757 : (M.op y y) = (τ (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e14 (M.op y y)
               have i₂ := b5e65736
               grind)
            | exact superpose b5e65736 b5e14
            | exact resolve b5e14 b5e65736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65736
          have b5e65834 : x = (M.op x y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e65757
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e65757
            | exact resolve b5e65757 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65757
          have b5e65938 : ∀ X0 : G, (M.op y x) = (M.op (M.op y x) X0) ∨ y = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b5e379 y x x
               have i₂ := b5e65834
               grind)
            | exact superpose b5e65834 b5e379
            | exact resolve b5e379 b5e65834
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e379 b5e65834
          have b5e65969 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b5e65938 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e65938
            | exact resolve b5e65938 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65938
          have b5e69368 : y ≠ y ∨ y = (M.op y y) := by
            first
            | (have j0 := b5e65969 y
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65969
          have b5e69369 : y = (M.op y y) := by grind
          clear b5e69368
          have b5e71647 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e93 y X1 x
               have i₂ := b5e69369
               grind)
            | exact superpose b5e69369 b5e93
            | exact resolve b5e93 b5e69369
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e93
          have b5e71683 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e13 y y x
               have i₂ := b5e69369
               grind)
            | exact superpose b5e69369 b5e13
            | exact resolve b5e13 b5e69369
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e71742 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e71683 X0
               have i₂ := b5e69369
               grind)
            | exact superpose b5e69369 b5e71683
            | exact resolve b5e71683 b5e69369
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69369 b5e71683
          have b5e83520 : ∀ X0 : G, (M.op y (M.op x y)) = (τ (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e6390 y
               have i₂ := b5e71647 (M.op x y) X0
               grind)
            | (have i₁ := b5e6390 y
               have i₂ := b5e71647 X0 (M.op x y)
               grind)
            | exact superpose b5e71647 b5e6390
            | exact resolve b5e6390 b5e71647
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6390
          have b5e83521 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e71647 (σ x) X0
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e71647 X0 (σ x)
               grind)
            | exact superpose b5e71647 b5e24
            | exact resolve b5e24 b5e71647
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71647
          have b5e83887 : ∀ X0 : G, y = (τ (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e83520 X0
               have i₂ := b5e71742 (M.op x y)
               grind)
            | exact superpose b5e71742 b5e83520
            | exact resolve b5e83520 b5e71742
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71742 b5e83520
          have b5e87750 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e15 (M.op (σ y) X0)
               have i₂ := b5e83887 X0
               grind)
            | exact superpose b5e83887 b5e15
            | exact resolve b5e15 b5e83887
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83887
          have b5e87771 : False := by grind
          exact b5e87771
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b7e32 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) X0) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ x) (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X0 X0))) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X0 X0) X2 X3
               have i₂ := b7e13 X0 X1 (M.op X0 X0)
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e40 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x x)) X0) := by
            intro X0
            first
            | (have i₁ := b7e32 X0
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e32
            | exact resolve b7e32 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e48 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e51 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e48
          have b7e52 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e51
               have r₂ := b7e23
               grind)
            | exact resolve b7e51 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e53 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e52
            | exact resolve b7e52 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e54 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e53
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e53
            | exact resolve b7e53 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e57 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e54
               grind)
            | exact superpose b7e54 b7e14
            | exact resolve b7e14 b7e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e58 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e57
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e57
            | exact resolve b7e57 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b7e64 : (σ (M.op x y)) = (σ (M.op x x)) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e54
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e54
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e54 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e65 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e22
               grind)
            | exact resolve b7e64 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e66 : (σ (M.op x y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e21
               grind)
            | exact resolve b7e65 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e68 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e58
               grind)
            | exact superpose b7e58 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e69 : (M.op x y) = (M.op x x) ∨ x = y := by
            first
            | (have r₁ := b7e68
               have r₂ := b7e22
               grind)
            | exact resolve b7e68 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e71 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b7e69
               have r₂ := b7e21
               grind)
            | exact resolve b7e69 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e85 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x y) X0) := by
            intro X0
            first
            | (have i₁ := b7e13 x x x
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e13
            | exact resolve b7e13 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e205 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) X0) := by
            intro X0
            first
            | (have i₁ := b7e40 X0
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e40
            | exact resolve b7e40 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e214 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (M.op (σ x) (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ (M.op x x)) X1
               have i₂ := b7e40 X0
               grind)
            | exact superpose b7e40 b7e13
            | exact resolve b7e13 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e219 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) (M.op X0 (σ (M.op x x)))) = (M.op (M.op (σ x) (σ y)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ (M.op x x)) X0 X1
               have i₂ := b7e40 (σ (M.op x x))
               grind)
            | exact superpose b7e40 b7e13
            | exact resolve b7e13 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e220 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X1) := by
            intro X1
            first
            | (have i₁ := b7e219 x X1
               have i₂ := b7e40 (M.op x (σ (M.op x x)))
               grind)
            | exact superpose b7e40 b7e219
            | exact resolve b7e219 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40 b7e219
          have b7e533 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ x) (σ x)) (M.op X0 (M.op (σ x) (σ x)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e37 (σ x) (σ y) X0 X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e37
            | exact resolve b7e37 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e621 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (σ x) (M.op (σ x) (σ y))) := by
            intro X1
            first
            | (have i₁ := b7e533 x X1
               have i₂ := b7e214 (σ x) (M.op x (M.op (σ x) (σ x)))
               grind)
            | exact superpose b7e214 b7e533
            | exact resolve b7e533 b7e214
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e214 b7e533
          have b7e659 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b7e621 x
               have i₂ := b7e220 x
               grind)
            | exact superpose b7e220 b7e621
            | exact resolve b7e621 b7e220
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e220 b7e621
          have b7e1213 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e62 y x
               grind)
            | exact superpose b7e62 b7e20
            | (have j1 := b7e62 y x
               grind)
            | exact resolve b7e20 b7e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1236 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have r₁ := b7e1213
               have r₂ := b7e23
               grind)
            | exact resolve b7e1213 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1213
          have b7e1265 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e1236
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e1236
            | exact resolve b7e1236 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1236
          have b7e1318 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) := by
            first
            | (have i₁ := b7e30 (M.op x y)
               have i₂ := b7e205 (σ (M.op x y))
               grind)
            | exact superpose b7e205 b7e30
            | exact resolve b7e30 b7e205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e205
          have b7e1358 : (M.op (σ x) (σ y)) = (σ (M.op x (M.op x y))) := by
            first
            | (have i₁ := b7e1318
               have i₂ := b7e85 (M.op x y)
               grind)
            | exact superpose b7e85 b7e1318
            | exact resolve b7e1318 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85 b7e1318
          have b7e6111 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e659
               have i₂ := b7e62 y x
               grind)
            | exact superpose b7e62 b7e659
            | (have j1 := b7e62 y x
               grind)
            | exact resolve b7e659 b7e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62 b7e659
          have b7e6133 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have r₁ := b7e6111
               have r₂ := b7e23
               grind)
            | exact resolve b7e6111 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6111
          have b7e6134 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have i₁ := b7e6133
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e6133
            | exact resolve b7e6133 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e6133
          have b7e6135 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have i₁ := b7e6134
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e6134
            | exact resolve b7e6134 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6134
          have b7e6136 : (σ y) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ x) := by
            first
            | (have i₁ := b7e6135
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e6135
            | exact resolve b7e6135 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6135
          have b7e6137 : (σ y) = (σ (k y x)) := by
            first
            | (have r₁ := b7e6136
               have r₂ := b7e1265
               grind)
            | exact resolve b7e6136 b7e1265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1265 b7e6136
          have b7e6139 : (k y x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e6137
               grind)
            | exact superpose b7e6137 b7e14
            | exact resolve b7e14 b7e6137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6137
          have b7e6158 : y = (k y x) := by
            first
            | (have i₁ := b7e6139
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e6139
            | exact resolve b7e6139 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6139
          have b7e6164 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e18 y x
               have i₂ := b7e6158
               grind)
            | exact superpose b7e6158 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e6158
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6158
          have b7e6165 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e6164
               have r₂ := b7e22
               grind)
            | exact resolve b7e6164 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6164
          have b7e6167 : x = (M.op x y) := by
            first
            | (have r₁ := b7e6165
               have r₂ := b7e21
               grind)
            | exact resolve b7e6165 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6165
          have b7e6244 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e1358
               have i₂ := b7e6167
               grind)
            | exact superpose b7e6167 b7e1358
            | exact resolve b7e1358 b7e6167
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1358 b7e6167
          have b7e6260 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e6244
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e6244
            | exact resolve b7e6244 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66 b7e6244
          have b7e6265 : False := by grind
          exact b7e6265
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
          have b8e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e864 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e61 x y
               grind)
            | exact superpose b8e61 b8e20
            | (have j1 := b8e61 x y
               grind)
            | exact resolve b8e20 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e905 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e864
               have r₂ := b8e24
               grind)
            | exact resolve b8e864 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e864
          have b8e922 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e905
               have r₂ := b8e23
               grind)
            | exact resolve b8e905 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e905
          have b8e929 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e922
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e922
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e922
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e922
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e922 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e922
          have b8e930 : y = (M.op y x) ∨ x = y := by grind
          clear b8e929
          have b8e931 : x = y := by
            first
            | (have r₁ := b8e930
               have r₂ := b8e22
               grind)
            | exact resolve b8e930 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e930
          have b8e932 : False := by grind
          exact b8e932
