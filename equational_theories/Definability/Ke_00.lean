import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1043`: `x = x ◇ ((y ◇ (x ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pxy_Equation1043 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1043 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1043.models_iff G M).mp hM
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
      have b0e59 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e61 : False := by grind
      exact b0e61
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e34 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
               have i₂ := b4e13 X0 X2 X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (M.op X1 (M.op X0 X2)) X0 X2
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e116 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (M.op (σ y) (M.op (M.op X0 (M.op (σ x) X1)) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e34 (σ x) (σ y) X0 X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e34
            | exact resolve b4e34 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e119 : ∀ X0 X1 : G, x = (M.op x (M.op y (M.op (M.op X0 (M.op x X1)) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e34 x y X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e34
            | exact resolve b4e34 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e130 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op (M.op X3 (M.op X0 X4)) X4)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e34 (M.op X1 X0) X2 X0 (M.op (M.op X3 (M.op X0 X4)) X4)
               have i₂ := b4e34 X0 X1 X3 X4
               grind)
            | exact superpose b4e34 b4e34
            | exact resolve b4e34 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e140 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e130 X0 X1 X2 x x
               have i₂ := b4e13 X0 x x
               grind)
            | exact superpose b4e13 b4e130
            | exact resolve b4e130 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130
          have b4e679 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e34 X0 X0 x X0
               have i₂ := b4e140 X0 X0 x
               grind)
            | exact superpose b4e140 b4e34
            | exact resolve b4e34 b4e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e708 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e140 X0 X0 X0
               have i₂ := b4e679 X0
               grind)
            | exact superpose b4e679 b4e140
            | exact resolve b4e140 b4e679
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e679
          have b4e987 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e140 (M.op X0 X0) (M.op X0 X0) x
               have i₂ := b4e708 X0
               grind)
            | exact superpose b4e708 b4e140
            | exact resolve b4e140 b4e708
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e140
          have b4e988 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e987 X0 X1
               have i₂ := b4e35 X0 X1 X0
               grind)
            | exact superpose b4e35 b4e987
            | exact resolve b4e987 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35 b4e987
          have b4e2992 : ∀ X0 : G, x = (M.op x (M.op y (M.op (M.op X0 X0) (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b4e119 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b4e988 X0 x
               grind)
            | exact superpose b4e988 b4e119
            | exact resolve b4e119 b4e988
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e119
          have b4e2993 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ y) (M.op (M.op X0 X0) (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b4e116 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b4e988 X0 (σ x)
               grind)
            | exact superpose b4e988 b4e116
            | exact resolve b4e116 b4e988
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e116
          have b4e2994 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b4e988 X0 X1
               grind)
            | exact superpose b4e988 b4e13
            | exact resolve b4e13 b4e988
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e988
          have b4e3031 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e2994 X0 X1
               have i₂ := b4e708 X0
               grind)
            | exact superpose b4e708 b4e2994
            | exact resolve b4e2994 b4e708
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2994
          have b4e3032 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ y) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e2993 X0
               have i₂ := b4e708 X0
               grind)
            | exact superpose b4e708 b4e2993
            | exact resolve b4e2993 b4e708
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2993
          have b4e3033 : ∀ X0 : G, x = (M.op x (M.op y (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e2992 X0
               have i₂ := b4e708 X0
               grind)
            | exact superpose b4e708 b4e2992
            | exact resolve b4e2992 b4e708
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e708 b4e2992
          have b4e3036 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e3032 x
               have i₂ := b4e3031 x (σ y)
               grind)
            | exact superpose b4e3031 b4e3032
            | exact resolve b4e3032 b4e3031
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3032
          have b4e3037 : x = (M.op x y) := by
            first
            | (have i₁ := b4e3033 x
               have i₂ := b4e3031 x y
               grind)
            | exact superpose b4e3031 b4e3033
            | exact resolve b4e3033 b4e3031
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3031 b4e3033
          have b4e3859 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e3036
               grind)
            | exact superpose b4e3036 b4e20
            | exact resolve b4e20 b4e3036
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3036
          have b4e3906 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e3859
               have i₂ := b4e3037
               grind)
            | exact superpose b4e3037 b4e3859
            | exact resolve b4e3859 b4e3037
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3037 b4e3859
          have b4e3907 : False := by grind
          exact b4e3907
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
            intro X0 X1 X2
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
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e33 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
               have i₂ := b5e13 X0 X2 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op X1 (M.op X0 X2)) X0 X2
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
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
          have b5e43 : x = y ∨ x = (k x y) := by grind
          clear b5e38
          have b5e44 : x = (k x y) := by
            first
            | (have r₁ := b5e43
               have r₂ := b5e21
               grind)
            | exact resolve b5e43 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b5e95 : ∀ X0 X1 : G, x = (M.op x (M.op y (M.op (M.op X0 (M.op x X1)) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 x y X0 X1
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e33
            | exact resolve b5e33 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e104 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op (M.op X3 (M.op X0 X4)) X4)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e33 (M.op X1 X0) X2 X0 (M.op (M.op X3 (M.op X0 X4)) X4)
               have i₂ := b5e33 X0 X1 X3 X4
               grind)
            | exact superpose b5e33 b5e33
            | exact resolve b5e33 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e112 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e104 X0 X1 X2 x x
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e104
            | exact resolve b5e104 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e104
          have b5e179 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e47 x y
               grind)
            | exact superpose b5e47 b5e20
            | (have j1 := b5e47 x y
               grind)
            | exact resolve b5e20 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e202 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b5e179
               have r₂ := b5e24
               grind)
            | exact resolve b5e179 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e179
          have b5e211 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b5e202
               have r₂ := b5e23
               grind)
            | exact resolve b5e202 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e202
          have b5e216 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e211
               have i₂ := b5e44
               grind)
            | exact superpose b5e44 b5e211
            | exact resolve b5e211 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e211
          have b5e604 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e33 X0 X0 x X0
               have i₂ := b5e112 X0 X0 x
               grind)
            | exact superpose b5e112 b5e33
            | exact resolve b5e33 b5e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e657 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e112 X0 X0 X0
               have i₂ := b5e604 X0
               grind)
            | exact superpose b5e604 b5e112
            | exact resolve b5e112 b5e604
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e604
          have b5e960 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e112 (M.op X0 X0) (M.op X0 X0) x
               have i₂ := b5e657 X0
               grind)
            | exact superpose b5e657 b5e112
            | exact resolve b5e112 b5e657
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e112
          have b5e961 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e960 X0 X1
               have i₂ := b5e34 X0 X1 X0
               grind)
            | exact superpose b5e34 b5e960
            | exact resolve b5e960 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e960
          have b5e2079 : ∀ X0 : G, x = (M.op x (M.op y (M.op (M.op X0 X0) (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b5e95 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b5e961 X0 x
               grind)
            | exact superpose b5e961 b5e95
            | exact resolve b5e95 b5e961
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95
          have b5e2080 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b5e961 X0 X1
               grind)
            | exact superpose b5e961 b5e13
            | exact resolve b5e13 b5e961
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e961
          have b5e2117 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e2080 X0 X1
               have i₂ := b5e657 X0
               grind)
            | exact superpose b5e657 b5e2080
            | exact resolve b5e2080 b5e657
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2080
          have b5e2118 : ∀ X0 : G, x = (M.op x (M.op y (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e2079 X0
               have i₂ := b5e657 X0
               grind)
            | exact superpose b5e657 b5e2079
            | exact resolve b5e2079 b5e657
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e657 b5e2079
          have b5e2121 : x = (M.op x y) := by
            first
            | (have i₁ := b5e2118 x
               have i₂ := b5e2117 x y
               grind)
            | exact superpose b5e2117 b5e2118
            | exact resolve b5e2118 b5e2117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2117 b5e2118
          have b5e2165 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e216
               have i₂ := b5e2121
               grind)
            | exact superpose b5e2121 b5e216
            | exact resolve b5e216 b5e2121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e216 b5e2121
          have b5e2197 : False := by grind
          exact b5e2197
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
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
          have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
               have i₂ := b7e13 X0 X2 X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 (M.op X1 (M.op X0 X2)) X0 X2
               have i₂ := b7e13 X0 X1 X2
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
          have b7e45 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e42
          have b7e46 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e45
               have r₂ := b7e23
               grind)
            | exact resolve b7e45 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
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
          have b7e61 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e51
               grind)
            | exact superpose b7e51 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e62 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e22
               grind)
            | exact resolve b7e61 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e64 : x = (M.op x y) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e21
               grind)
            | exact resolve b7e62 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e109 : ∀ X0 X1 : G, y = (M.op y (M.op x (M.op (M.op X0 (M.op y X1)) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e33 y x X0 X1
               have i₂ := b7e64
               grind)
            | exact superpose b7e64 b7e33
            | exact resolve b7e33 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e118 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op (M.op X3 (M.op X0 X4)) X4)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e33 (M.op X1 X0) X2 X0 (M.op (M.op X3 (M.op X0 X4)) X4)
               have i₂ := b7e33 X0 X1 X3 X4
               grind)
            | exact superpose b7e33 b7e33
            | exact resolve b7e33 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e124 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e118 X0 X1 X2 x x
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e118
            | exact resolve b7e118 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e118
          have b7e728 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e33 X0 X0 x X0
               have i₂ := b7e124 X0 X0 x
               grind)
            | exact superpose b7e124 b7e33
            | exact resolve b7e33 b7e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e787 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e124 X0 X0 X0
               have i₂ := b7e728 X0
               grind)
            | exact superpose b7e728 b7e124
            | exact resolve b7e124 b7e728
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e728
          have b7e1198 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e124 (M.op X0 X0) (M.op X0 X0) x
               have i₂ := b7e787 X0
               grind)
            | exact superpose b7e787 b7e124
            | exact resolve b7e124 b7e787
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e124
          have b7e1199 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e1198 X0 X1
               have i₂ := b7e34 X0 X1 X0
               grind)
            | exact superpose b7e34 b7e1198
            | exact resolve b7e1198 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e1198
          have b7e2287 : ∀ X0 : G, y = (M.op y (M.op x (M.op (M.op X0 X0) (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b7e109 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b7e1199 X0 y
               grind)
            | exact superpose b7e1199 b7e109
            | exact resolve b7e109 b7e1199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e109
          have b7e2289 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b7e1199 X0 X1
               grind)
            | exact superpose b7e1199 b7e13
            | exact resolve b7e13 b7e1199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1199
          have b7e2324 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e2289 X0 X1
               have i₂ := b7e787 X0
               grind)
            | exact superpose b7e787 b7e2289
            | exact resolve b7e2289 b7e787
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2289
          have b7e2326 : ∀ X0 : G, y = (M.op y (M.op x (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b7e2287 X0
               have i₂ := b7e787 X0
               grind)
            | exact superpose b7e787 b7e2287
            | exact resolve b7e2287 b7e787
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e787 b7e2287
          have b7e2330 : y = (M.op y x) := by
            first
            | (have i₁ := b7e2326 x
               have i₂ := b7e2324 x x
               grind)
            | exact superpose b7e2324 b7e2326
            | exact resolve b7e2326 b7e2324
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2324 b7e2326
          have b7e2331 : False := by grind
          exact b7e2331
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
          have b8e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e131 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e56 x y
               grind)
            | exact superpose b8e56 b8e20
            | (have j1 := b8e56 x y
               grind)
            | exact resolve b8e20 b8e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e154 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e131
               have r₂ := b8e24
               grind)
            | exact resolve b8e131 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e131
          have b8e159 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e154
               have r₂ := b8e23
               grind)
            | exact resolve b8e154 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e154
          have b8e160 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e159
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e159
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e159
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e159
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e159 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e159
          have b8e161 : y = (M.op y x) ∨ x = y := by grind
          clear b8e160
          have b8e162 : x = y := by
            first
            | (have r₁ := b8e161
               have r₂ := b8e22
               grind)
            | exact resolve b8e161 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e161
          have b8e163 : False := by grind
          exact b8e163

/-- `Equation106`: `x = x ◇ ((y ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_pyx_pxy_Equation106 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law106 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law106.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e25 : ∀ X0 : G, x = (M.op x (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e11 x x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e28 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X0 (M.op (M.op x (M.op X0 X1)) x)
           have i₂ := b0e11 (M.op X0 X1) x x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : x = (M.op x y) := by
        first
        | (have i₁ := b0e25 (M.op (M.op x y) x)
           have i₂ := b0e11 y x x
           grind)
        | exact superpose b0e11 b0e25
        | exact resolve b0e25 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25
      have b0e45 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e28 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e28
        | exact resolve b0e28 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e168 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e45
           grind)
        | exact superpose b0e45 b0e18
        | exact resolve b0e18 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e176 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e168
           have i₂ := b0e31
           grind)
        | exact superpose b0e31 b0e168
        | exact resolve b0e168 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31 b0e168
      have b0e177 : False := by grind
      exact b0e177
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : x = (k x y) := by grind
        have b1e25 : ∀ X0 : G, x = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 x x X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : x = (M.op x y) := by
          first
          | (have i₁ := b1e25 (M.op (M.op x y) x)
             have i₂ := b1e12 y x x
             grind)
          | exact superpose b1e12 b1e25
          | exact resolve b1e25 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e46 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e51 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e46
        have b1e54 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e51
             have r₂ := b1e21
             grind)
          | exact resolve b1e51 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e55 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e54
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e54
          | exact resolve b1e54 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e56 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e55
             have i₂ := b1e24
             grind)
          | exact superpose b1e24 b1e55
          | exact resolve b1e55 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e55
        have b1e57 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e19
          | exact resolve b1e19 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e58 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e22
          | exact resolve b1e22 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e65 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e57
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e57
          | exact resolve b1e57 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e58
        have b1e66 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e65
             have i₂ := b1e29
             grind)
          | exact superpose b1e29 b1e65
          | exact resolve b1e65 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29 b1e65
        have b1e67 : False := by grind
        exact b1e67
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b2e24 : x = (k x y) := by grind
        have b2e27 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 (M.op (M.op x (M.op X0 X1)) x)
             have i₂ := b2e12 (M.op X0 X1) x x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b2e415 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e59 x y
             grind)
          | exact superpose b2e59 b2e22
          | (have j1 := b2e59 x y
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e59 x y
             grind)
          | exact resolve b2e22 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e431 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
        clear b2e415
        have b2e442 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have r₁ := b2e431
             have r₂ := b2e21
             grind)
          | exact resolve b2e431 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e431
        have b2e451 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e442
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e442
          | exact resolve b2e442 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e442
        have b2e457 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e27 (σ x) (σ y)
             have i₂ := b2e451
             grind)
          | exact superpose b2e451 b2e27
          | exact resolve b2e27 b2e451
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e451
        have b2e463 : False := by grind
        exact b2e463
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ x) = (k (σ x) (σ y)) := by grind
        have b3e25 : (σ x) = (σ (k x y)) := by
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
        have b3e26 : (k x y) = (τ (σ x)) := by
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
        have b3e27 : x = (k x y) := by
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
        have b3e28 : ∀ X0 : G, x = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 x y X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : x = (M.op x y) := by
          first
          | (have i₁ := b3e28 (M.op (M.op x y) x)
             have i₂ := b3e12 y x x
             grind)
          | exact superpose b3e12 b3e28
          | exact resolve b3e28 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e46 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) := by
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
        have b3e47 : y = (M.op x x) ∨ y = (k x y) := by grind
        clear b3e46
        have b3e51 : y = (k x y) := by
          first
          | (have r₁ := b3e47
             have r₂ := b3e20
             grind)
          | exact resolve b3e47 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e52 : x = y := by
          first
          | (have i₁ := b3e51
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e51
          | exact resolve b3e51 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e51
        have b3e53 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e52
             grind)
          | exact superpose b3e52 b3e19
          | exact resolve b3e19 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e58 : x = (M.op x x) := by
          first
          | (have i₁ := b3e39
             have i₂ := b3e52
             grind)
          | exact superpose b3e52 b3e39
          | exact resolve b3e39 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e59 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e53
             have i₂ := b3e58
             grind)
          | exact superpose b3e58 b3e53
          | exact resolve b3e53 b3e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e58
        have b3e60 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e59
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e59
          | exact resolve b3e59 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
        have b3e61 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e60
             have i₂ := b3e52
             grind)
          | exact superpose b3e52 b3e60
          | exact resolve b3e60 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52 b3e60
        have b3e62 : False := by grind
        exact b3e62
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : ∀ X0 : G, x = (M.op x (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 x y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e29 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0 (M.op (M.op x (M.op X0 X1)) x)
               have i₂ := b4e13 (M.op X0 X1) x x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e31 : x = (M.op x y) := by
            first
            | (have i₁ := b4e26 (M.op (M.op x y) x)
               have i₂ := b4e13 y x x
               grind)
            | exact superpose b4e13 b4e26
            | exact resolve b4e26 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e38 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e29 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e29
            | exact resolve b4e29 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29
          have b4e88 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e38
               grind)
            | exact superpose b4e38 b4e20
            | exact resolve b4e20 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e94 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e88
               have i₂ := b4e31
               grind)
            | exact superpose b4e31 b4e88
            | exact resolve b4e88 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e88
          have b4e95 : False := by grind
          exact b4e95
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b5e26 : ∀ X0 : G, x = (M.op x (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 x y X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e28 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 (M.op (M.op x (M.op X0 X1)) x)
               have i₂ := b5e13 (M.op X0 X1) x x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : x = (M.op x y) := by
            first
            | (have i₁ := b5e26 (M.op (M.op x y) x)
               have i₂ := b5e13 y x x
               grind)
            | exact superpose b5e13 b5e26
            | exact resolve b5e26 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e28 X0 (M.op X1 X0)
               have i₂ := b5e28 X1 X0
               grind)
            | exact superpose b5e28 b5e28
            | exact resolve b5e28 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op X1 X0) X0 X2
               have i₂ := b5e28 X1 X0
               grind)
            | exact superpose b5e28 b5e13
            | exact resolve b5e13 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) := by
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
          have b5e46 : ∀ X0 : G, x ≠ x ∨ x = (M.op (M.op y X0) (M.op y X0)) ∨ x = (k (M.op y X0) x) := by
            intro X0
            first
            | (have i₁ := b5e17 (M.op y X0) x
               have i₂ := b5e26 X0
               grind)
            | exact superpose b5e26 b5e17
            | (have j0 := b5e17 (M.op y X0) x
               grind)
            | (have r₁ := b5e17 (M.op y X0) x
               have r₂ := b5e26 X0
               grind)
            | exact resolve b5e17 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26
          have b5e49 : ∀ X0 : G, x = (M.op (M.op y X0) (M.op y X0)) ∨ x = (k (M.op y X0) x) := by
            intro X0
            first
            | (have j0 := b5e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e52 : y = (M.op x x) ∨ y = (k x y) := by grind
          clear b5e43
          have b5e53 : y = (k x y) := by
            first
            | (have r₁ := b5e52
               have r₂ := b5e21
               grind)
            | exact resolve b5e52 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e389 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e28 (σ X0) (σ X1)
               have i₂ := b5e57 X0 X1
               grind)
            | exact superpose b5e57 b5e28
            | (have j1 := b5e57 X0 X1
               grind)
            | exact resolve b5e28 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e415 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e57 x y
               grind)
            | exact superpose b5e57 b5e24
            | (have j1 := b5e57 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e57 x y
               grind)
            | exact resolve b5e24 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e431 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
          clear b5e415
          have b5e442 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e431
               have r₂ := b5e23
               grind)
            | exact resolve b5e431 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e431
          have b5e451 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e442
               have i₂ := b5e53
               grind)
            | exact superpose b5e53 b5e442
            | exact resolve b5e442 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53 b5e442
          have b5e452 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e451
               grind)
            | exact superpose b5e451 b5e20
            | exact resolve b5e20 b5e451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e458 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e37 (σ y) (σ x)
               have i₂ := b5e451
               grind)
            | exact superpose b5e451 b5e37
            | exact resolve b5e37 b5e451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e463 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e452
               have i₂ := b5e30
               grind)
            | exact superpose b5e30 b5e452
            | exact resolve b5e452 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e452
          have b5e523 : (σ y) = (k (σ y) (σ y)) := by grind
          have b5e533 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b5e523
               have i₂ := b5e19 y y
               grind)
            | exact superpose b5e19 b5e523
            | exact resolve b5e523 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e523
          have b5e590 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e28 (M.op X0 X1) (M.op X1 X2)
               have i₂ := b5e41 X1 X0 X2
               grind)
            | exact superpose b5e41 b5e28
            | exact resolve b5e28 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e603 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b5e14 (k y y)
               have i₂ := b5e533
               grind)
            | exact superpose b5e533 b5e14
            | exact resolve b5e14 b5e533
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e533
          have b5e621 : y = (k y y) := by
            first
            | (have i₁ := b5e603
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e603
            | exact resolve b5e603 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e603
          have b5e678 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e18 y y
               have i₂ := b5e621
               grind)
            | exact superpose b5e621 b5e18
            | (have j0 := b5e18 y y
               grind)
            | exact resolve b5e18 b5e621
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e621
          have b5e679 : y = (M.op y y) := by grind
          clear b5e678
          have b5e1628 : x = (M.op y y) ∨ x = (k (M.op y y) x) := by
            first
            | (have i₁ := b5e41 y y y
               have i₂ := b5e49 y
               grind)
            | exact superpose b5e49 b5e41
            | (have j1 := b5e49 y
               grind)
            | exact resolve b5e41 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e49
          have b5e1663 : x = y ∨ x = (k (M.op y y) x) := by
            first
            | (have i₁ := b5e1628
               have i₂ := b5e679
               grind)
            | exact superpose b5e679 b5e1628
            | exact resolve b5e1628 b5e679
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1628
          have b5e1665 : x = (k y x) ∨ x = y := by
            first
            | (have i₁ := b5e1663
               have i₂ := b5e679
               grind)
            | exact superpose b5e679 b5e1663
            | exact resolve b5e1663 b5e679
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e679 b5e1663
          have b5e1784 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b5e590 X0 (σ x) (σ y)
               have i₂ := b5e451
               grind)
            | exact superpose b5e451 b5e590
            | exact resolve b5e590 b5e451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e590
          have b5e4853 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b5e389 y x
               have i₂ := b5e1665
               grind)
            | exact superpose b5e1665 b5e389
            | (have j0 := b5e389 x x
               grind)
            | exact resolve b5e389 b5e1665
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e389 b5e1665
          have b5e5047 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b5e4853
               have i₂ := b5e458
               grind)
            | exact superpose b5e458 b5e4853
            | exact resolve b5e4853 b5e458
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e458 b5e4853
          have b5e5061 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
            first
            | (have r₁ := b5e5047
               have r₂ := b5e463
               grind)
            | exact resolve b5e5047 b5e463
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5047
          have b5e5069 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e5061
               have i₂ := b5e451
               grind)
            | exact superpose b5e451 b5e5061
            | exact resolve b5e5061 b5e451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e451 b5e5061
          have b5e5074 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have r₁ := b5e5069
               have r₂ := b5e463
               grind)
            | exact resolve b5e5069 b5e463
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5069
          have b5e5415 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e1784 (σ x)
               have i₂ := b5e5074
               grind)
            | exact superpose b5e5074 b5e1784
            | exact resolve b5e1784 b5e5074
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1784 b5e5074
          have b5e5453 : x = y := by
            first
            | (have r₁ := b5e5415
               have r₂ := b5e24
               grind)
            | exact resolve b5e5415 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5415
          have b5e6159 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e463
               have i₂ := b5e5453
               grind)
            | exact superpose b5e5453 b5e463
            | exact resolve b5e463 b5e5453
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e463 b5e5453
          have b5e6177 : False := by grind
          exact b5e6177
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b6e30 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 X0 (M.op (M.op x (M.op X0 X1)) x)
             have i₂ := b6e12 (M.op X0 X1) x x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e37 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e30 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e30
          | exact resolve b6e30 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e42 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e37
             grind)
          | exact superpose b6e37 b6e19
          | exact resolve b6e19 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e58 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
        have b6e66 : y = (M.op x x) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e58
             have r₂ := b6e42
             grind)
          | exact resolve b6e58 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e58
        have b6e69 : y = (M.op y x) := by
          first
          | (have r₁ := b6e66
             have r₂ := b6e20
             grind)
          | exact resolve b6e66 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e72 : False := by grind
        exact b6e72
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b7e28 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X0 (M.op (M.op x (M.op X0 X1)) x)
               have i₂ := b7e13 (M.op X0 X1) x x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e28 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e28
            | exact resolve b7e28 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e38 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e29
               grind)
            | exact superpose b7e29 b7e20
            | exact resolve b7e20 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e39 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e42 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = X0 ∨ (k (M.op X1 X0) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e17 (M.op X0 X1) X1
               have i₂ := b7e28 X0 X1
               grind)
            | exact superpose b7e28 b7e17
            | (have j0 := b7e17 (M.op X1 X0) X0
               grind)
            | (have r₁ := b7e17 (M.op X0 X1) X1
               have r₂ := b7e28 X0 X1
               grind)
            | exact resolve b7e17 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e43 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = X0 ∨ (k (M.op X1 X0) X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e42 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e46 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e39
          have b7e48 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e46
               have r₂ := b7e23
               grind)
            | exact resolve b7e46 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e49 : (σ y) = (σ (k x y)) := by
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
          have b7e52 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e49
               grind)
            | exact superpose b7e49 b7e14
            | exact resolve b7e14 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e53 : y = (k x y) := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e52
            | exact resolve b7e52 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
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
          have b7e60 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e69 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e53
               grind)
            | exact superpose b7e53 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e70 : y = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e69
               have r₂ := b7e21
               grind)
            | exact resolve b7e69 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e72 : y = (M.op x y) := by
            first
            | (have r₁ := b7e70
               have r₂ := b7e22
               grind)
            | exact resolve b7e70 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e82 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e38
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e38
            | exact resolve b7e38 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38
          have b7e84 : y = (M.op y y) := by
            first
            | (have i₁ := b7e28 x y
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e28
            | exact resolve b7e28 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e85 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 y x X0
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e13
            | exact resolve b7e13 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e103 : y = (k y y) := by grind
          clear b7e84
          have b7e397 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e58 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e398 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e397 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e397
          have b7e1724 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e398 y
               have i₂ := b7e103
               grind)
            | exact superpose b7e103 b7e398
            | (have j0 := b7e398 y
               grind)
            | exact resolve b7e398 b7e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e103 b7e398
          have b7e1728 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b7e1724
          have b7e1814 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e43 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e43
            | exact resolve b7e43 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e1886 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e1814
               have i₂ := b7e1728
               grind)
            | exact superpose b7e1728 b7e1814
            | exact resolve b7e1814 b7e1728
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1728 b7e1814
          have b7e1890 : (σ x) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b7e1886
               have r₂ := b7e82
               grind)
            | exact resolve b7e1886 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1886
          have b7e1891 : (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b7e1890
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e1890
            | exact resolve b7e1890 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1890
          have b7e1896 : (k y x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e1891
               grind)
            | exact superpose b7e1891 b7e14
            | exact resolve b7e14 b7e1891
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1891
          have b7e1927 : x = (k y x) := by
            first
            | (have i₁ := b7e1896
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1896
            | exact resolve b7e1896 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1896
          have b7e2011 : x = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e60 x y
               have i₂ := b7e1927
               grind)
            | exact superpose b7e1927 b7e60
            | (have j0 := b7e60 x y
               grind)
            | exact resolve b7e60 b7e1927
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60 b7e1927
          have b7e2014 : x = y ∨ x = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e2011
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e2011
            | exact resolve b7e2011 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72 b7e2011
          have b7e2015 : x = (M.op y x) ∨ x = y := by grind
          clear b7e2014
          have b7e2185 : y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e85 x
               have i₂ := b7e2015
               grind)
            | exact superpose b7e2015 b7e85
            | exact resolve b7e85 b7e2015
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85 b7e2015
          have b7e2210 : x = y := by
            first
            | (have r₁ := b7e2185
               have r₂ := b7e22
               grind)
            | exact resolve b7e2185 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2185
          have b7e2299 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b7e82
               have i₂ := b7e2210
               grind)
            | exact superpose b7e2210 b7e82
            | exact resolve b7e82 b7e2210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82 b7e2210
          have b7e2314 : False := by grind
          exact b7e2314
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
          have b8e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b8e337 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e63 x y
               grind)
            | exact superpose b8e63 b8e24
            | (have j1 := b8e63 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e63 x y
               grind)
            | exact resolve b8e24 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e355 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
          clear b8e337
          have b8e367 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e355
               have r₂ := b8e23
               grind)
            | exact resolve b8e355 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e355
          have b8e377 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e367
               grind)
            | exact superpose b8e367 b8e20
            | exact resolve b8e20 b8e367
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e367
          have b8e427 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e377
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e377
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e377 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e377
          have b8e428 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e427
          have b8e429 : y = (M.op y x) := by
            first
            | (have r₁ := b8e428
               have r₂ := b8e21
               grind)
            | exact resolve b8e428 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e428
          have b8e430 : False := by grind
          exact b8e430

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pyx_y_pxy_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
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
      have b0e28 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 := by
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
      have b0e32 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e28 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e28
        | exact resolve b0e28 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e33 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e27 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e27
        | exact resolve b0e27 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27
      have b0e34 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e32 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e32
        | exact resolve b0e32 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e35 : ∀ X0 : G, (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e33 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e33
        | exact resolve b0e33 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e49 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e34 (σ x)
           grind)
        | exact superpose b0e34 b0e18
        | exact resolve b0e18 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e51 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e49
           have i₂ := b0e35 x
           grind)
        | exact superpose b0e35 b0e49
        | exact resolve b0e49 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e49
      have b0e52 : False := by grind
      exact b0e52
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ x)) (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e26 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e26
          | exact resolve b1e26 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e31 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e25 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e25
          | exact resolve b1e25 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e32 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e30 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e30
          | exact resolve b1e30 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e33 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e31 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e31
          | exact resolve b1e31 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e37 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | (have j0 := b1e15 X0 (σ x)
             grind)
          | (have r₁ := b1e15 X0 (σ x)
             have r₂ := b1e22
             grind)
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b1e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e78 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 x
             have i₂ := b1e42 (σ X0)
             grind)
          | exact superpose b1e42 b1e18
          | exact resolve b1e18 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e526 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e78 y
             grind)
          | exact superpose b1e78 b1e19
          | exact resolve b1e19 b1e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e529 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b1e32 (σ x)
             have i₂ := b1e78 x
             grind)
          | exact superpose b1e78 b1e32
          | exact resolve b1e32 b1e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32 b1e78
        have b1e544 : (σ x) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e526
             have i₂ := b1e33 x
             grind)
          | exact superpose b1e33 b1e526
          | exact resolve b1e526 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e526
        have b1e610 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (k x x)
             have i₂ := b1e529
             grind)
          | exact superpose b1e529 b1e13
          | exact resolve b1e13 b1e529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e529
        have b1e612 : x = (k x x) := by
          first
          | (have i₁ := b1e610
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e610
          | exact resolve b1e610 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e610
        have b1e661 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e612
             grind)
          | exact superpose b1e612 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e612
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e612
        have b1e662 : x = (M.op x x) := by grind
        clear b1e661
        have b1e734 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 x
             have i₂ := b1e662
             grind)
          | exact superpose b1e662 b1e15
          | (have j0 := b1e15 X0 x
             grind)
          | (have r₁ := b1e15 X0 x
             have r₂ := b1e662
             grind)
          | exact resolve b1e15 b1e662
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e662
        have b1e743 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b1e734 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e734
        have b1e1317 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e544
             have i₂ := b1e743 y
             grind)
          | exact superpose b1e743 b1e544
          | exact resolve b1e544 b1e743
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e544 b1e743
        have b1e1319 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e1317
             have i₂ := b1e33 x
             grind)
          | exact superpose b1e33 b1e1317
          | exact resolve b1e1317 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e1317
        have b1e1320 : False := by grind
        exact b1e1320
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e74 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X0 X2
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X0
             have j1 := b2e17 X2 X2
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e82 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e74 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e74
        have b2e623 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e82 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e624 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e623 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e623
        have b2e634 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e624 X0
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e624 x
             have r₂ := b2e15 X0 x
             grind)
          | exact resolve b2e624 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e624
        have b2e644 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e634 (σ X0)
             grind)
          | exact superpose b2e634 b2e18
          | exact resolve b2e18 b2e634
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e654 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e644 X0
             have i₂ := b2e634 X0
             grind)
          | exact superpose b2e634 b2e644
          | exact resolve b2e644 b2e634
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e634 b2e644
        have b2e1213 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e654 y
             grind)
          | exact superpose b2e654 b2e21
          | exact resolve b2e21 b2e654
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e654
        have b2e1243 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e1213
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1213
          | exact resolve b2e1213 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1213
        have b2e1244 : False := by grind
        exact b2e1244
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ y) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e26 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e26
          | exact resolve b3e26 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e32 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e30 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e30
          | exact resolve b3e30 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e37 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
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
        have b3e42 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have j0 := b3e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e75 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e42 (σ X0)
             grind)
          | exact superpose b3e42 b3e18
          | exact resolve b3e18 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e485 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e32 (σ y)
             have i₂ := b3e75 y
             grind)
          | exact superpose b3e75 b3e32
          | exact resolve b3e32 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32 b3e75
        have b3e563 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e485
             grind)
          | exact superpose b3e485 b3e13
          | exact resolve b3e13 b3e485
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e485
        have b3e565 : y = (k y y) := by
          first
          | (have i₁ := b3e563
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e563
          | exact resolve b3e563 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e563
        have b3e613 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e565
             grind)
          | exact superpose b3e565 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e565
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e565
        have b3e614 : y = (M.op y y) := by grind
        clear b3e613
        have b3e616 : False := by grind
        exact b3e616
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x x) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e31 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) x)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e31 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e31
            | exact resolve b4e31 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e39 : ∀ X0 : G, (M.op X0 x) = X0 := by
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
          have b4e43 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e16 X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | (have j0 := b4e16 X0 (σ x)
               grind)
            | (have r₁ := b4e16 X0 (σ x)
               have r₂ := b4e24
               grind)
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b4e16 X0 x
               have i₂ := b4e39 x
               grind)
            | exact superpose b4e39 b4e16
            | (have j0 := b4e16 X0 x
               grind)
            | (have r₁ := b4e16 X0 x
               have r₂ := b4e39 x
               grind)
            | exact resolve b4e16 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e46 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b4e45 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e48 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e43 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e87 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 x
               have i₂ := b4e48 (σ X0)
               grind)
            | exact superpose b4e48 b4e19
            | exact resolve b4e19 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e90 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e87 X0
               have i₂ := b4e46 X0
               grind)
            | exact superpose b4e46 b4e87
            | exact resolve b4e87 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46 b4e87
          have b4e807 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e90 y
               grind)
            | exact superpose b4e90 b4e20
            | (have r₁ := b4e20
               have r₂ := b4e90 y
               grind)
            | exact resolve b4e20 b4e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90
          have b4e824 : False := by grind
          exact b4e824
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op x x) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e81 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 X1 X0
               have i₂ := b5e18 X0 X2
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X1 X0
               have j1 := b5e18 X2 X2
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X0 X0
               have r₂ := b5e18 X0 X1
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e90 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e81 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e639 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e90 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90
          have b5e640 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e639 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e639
          have b5e650 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e640 X0
               have j1 := b5e16 X0 X0
               grind)
            | (have r₁ := b5e640 x
               have r₂ := b5e16 X0 x
               grind)
            | exact resolve b5e640 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e640
          have b5e660 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e650 (σ X0)
               grind)
            | exact superpose b5e650 b5e19
            | exact resolve b5e19 b5e650
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e670 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e660 X0
               have i₂ := b5e650 X0
               grind)
            | exact superpose b5e650 b5e660
            | exact resolve b5e660 b5e650
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e650 b5e660
          have b5e1073 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e670 x
               grind)
            | exact superpose b5e670 b5e24
            | exact resolve b5e24 b5e670
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e670
          have b5e1100 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e1073
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1073
            | exact resolve b5e1073 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1073
          have b5e1101 : False := by grind
          exact b5e1101
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 := by
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
        have b6e29 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
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
        have b6e30 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
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
        have b6e36 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e15 X0 (σ y)
             have i₂ := b6e30 (σ y)
             grind)
          | exact superpose b6e30 b6e15
          | (have j0 := b6e15 X0 (σ y)
             grind)
          | (have r₁ := b6e15 X0 (σ y)
             have r₂ := b6e30 (σ y)
             grind)
          | exact resolve b6e15 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e37 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e36 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e47 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 y
             have i₂ := b6e37 (σ X0)
             grind)
          | exact superpose b6e37 b6e18
          | exact resolve b6e18 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e369 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e30 (σ y)
             have i₂ := b6e47 y
             grind)
          | exact superpose b6e47 b6e30
          | exact resolve b6e30 b6e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30 b6e47
        have b6e423 : (τ (σ y)) = (k y y) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e369
             grind)
          | exact superpose b6e369 b6e13
          | exact resolve b6e13 b6e369
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e369
        have b6e425 : y = (k y y) := by
          first
          | (have i₁ := b6e423
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e423
          | exact resolve b6e423 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e423
        have b6e492 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e425
             grind)
          | exact superpose b6e425 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e425
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e425
        have b6e493 : y = (M.op y y) := by grind
        clear b6e492
        have b6e497 : False := by grind
        exact b6e497
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x x) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e31 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ x)) (σ x))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ x) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 := by
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
          have b7e36 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e35 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e35
            | exact resolve b7e35 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e41 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e16 X0 (σ x)
               have i₂ := b7e36 (σ x)
               grind)
            | exact superpose b7e36 b7e16
            | (have j0 := b7e16 X0 (σ x)
               grind)
            | (have r₁ := b7e16 X0 (σ x)
               have r₂ := b7e36 (σ x)
               grind)
            | exact resolve b7e16 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e42 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b7e41 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e46 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 x
               have i₂ := b7e42 (σ X0)
               grind)
            | exact superpose b7e42 b7e19
            | exact resolve b7e19 b7e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e290 : (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b7e36 (σ x)
               have i₂ := b7e46 x
               grind)
            | exact superpose b7e46 b7e36
            | exact resolve b7e36 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36 b7e46
          have b7e387 : (τ (σ x)) = (k x x) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e290
               grind)
            | exact superpose b7e290 b7e14
            | exact resolve b7e14 b7e290
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e290
          have b7e389 : x = (k x x) := by
            first
            | (have i₁ := b7e387
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e387
            | exact resolve b7e387 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e387
          have b7e448 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x x
               have i₂ := b7e389
               grind)
            | exact superpose b7e389 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e389
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e389
          have b7e449 : x = (M.op x x) := by grind
          clear b7e448
          have b7e451 : False := by grind
          exact b7e451
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b8e76 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ x) X0
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 X0 (σ x)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) x
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e82 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b8e76 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e120 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 x X0
               have i₂ := b8e82 (σ X0)
               grind)
            | exact superpose b8e82 b8e19
            | (have j1 := b8e82 (σ X0)
               grind)
            | exact resolve b8e19 b8e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82
          have b8e5130 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e120 y
               grind)
            | exact superpose b8e120 b8e23
            | (have j1 := b8e120 y
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e120 y
               grind)
            | exact resolve b8e23 b8e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e120
          have b8e5164 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
          clear b8e5130
          have b8e5242 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e5164
               grind)
            | exact superpose b8e5164 b8e20
            | exact resolve b8e20 b8e5164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5164
          have b8e5437 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e5242
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e5242
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e5242 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5242
          have b8e5449 : y = (M.op y y) ∨ x = (M.op x x) := by grind
          clear b8e5437
          have b8e5456 : x = (M.op x x) := by
            first
            | (have r₁ := b8e5449
               have r₂ := b8e21
               grind)
            | exact resolve b8e5449 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5449
          have b8e5457 : False := by grind
          exact b8e5457

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pxy_pyx_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e29 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
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
      have b0e30 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 := by
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
      have b0e36 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
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
      have b0e37 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e29 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e29
        | exact resolve b0e29 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e38 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e36 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e36
        | exact resolve b0e36 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e39 : ∀ X0 : G, (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e37 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e37
        | exact resolve b0e37 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e56 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e38 (σ x)
           grind)
        | exact superpose b0e38 b0e18
        | exact resolve b0e18 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e59 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e56
           have i₂ := b0e39 x
           grind)
        | exact superpose b0e39 b0e56
        | exact resolve b0e56 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e56
      have b0e60 : False := by grind
      exact b0e60
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
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
        have b1e37 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e45 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e37 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e37
          | exact resolve b1e37 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e47 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e45 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e45
          | exact resolve b1e45 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e53 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e16 (σ x) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) X0
             grind)
          | (have r₁ := b1e16 (σ x) x
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e58 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b1e53 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e93 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
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
        have b1e101 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e93 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e93
          | exact resolve b1e93 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e93
        have b1e188 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e101 (σ x)
             have i₂ := b1e58 (σ y)
             grind)
          | exact superpose b1e58 b1e101
          | (have j1 := b1e58 (σ y)
             grind)
          | exact resolve b1e101 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58 b1e101
        have b1e199 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b1e188
             have r₂ := b1e21
             grind)
          | exact resolve b1e188 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e188
        have b1e201 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e199
             grind)
          | exact superpose b1e199 b1e19
          | exact resolve b1e19 b1e199
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e199
        have b1e208 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e201
             have i₂ := b1e47 x
             grind)
          | exact superpose b1e47 b1e201
          | exact resolve b1e201 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47 b1e201
        have b1e209 : False := by grind
        exact b1e209
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
        have b2e76 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ y) X0
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
        have b2e81 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b2e76 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76
        have b2e109 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
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
        have b2e114 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e109 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e109
          | exact resolve b2e109 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e109
        have b2e244 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e114 (σ y)
             have i₂ := b2e81 (σ y)
             grind)
          | exact superpose b2e81 b2e114
          | (have j1 := b2e81 (σ y)
             grind)
          | exact resolve b2e114 b2e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e81 b2e114
        have b2e247 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e244
        have b2e251 : False := by grind
        exact b2e251
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b3e38 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ y) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e38 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e38
          | exact resolve b3e38 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e46 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e44 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e44
          | exact resolve b3e44 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e53 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e16 (σ y) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e16
          | (have j0 := b3e16 (σ y) X0
             grind)
          | (have r₁ := b3e16 (σ y) x
             have r₂ := b3e22
             grind)
          | exact resolve b3e16 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e58 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have j0 := b3e53 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e183 : (σ y) = (M.op (σ y) y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e34 (σ y)
             have i₂ := b3e58 y
             grind)
          | exact superpose b3e58 b3e34
          | (have j1 := b3e58 y
             grind)
          | exact resolve b3e34 b3e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e58
        have b3e192 : (σ y) = (M.op (σ y) y) := by
          first
          | (have r₁ := b3e183
             have r₂ := b3e20
             grind)
          | exact resolve b3e183 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e183
        have b3e196 : ∀ X0 : G, (M.op X0 (M.op (M.op y (σ y)) (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y (σ y)
             have i₂ := b3e192
             grind)
          | exact superpose b3e192 b3e12
          | exact resolve b3e12 b3e192
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e192
        have b3e197 : ∀ X0 : G, (M.op X0 (M.op y (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e196 X0
             have i₂ := b3e46 (M.op y (σ y))
             grind)
          | exact superpose b3e46 b3e196
          | exact resolve b3e196 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e196
        have b3e200 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e197 X0
             have i₂ := b3e46 y
             grind)
          | exact superpose b3e46 b3e197
          | exact resolve b3e197 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46 b3e197
        have b3e274 : y ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e200 y
             grind)
          | exact superpose b3e200 b3e20
          | (have r₁ := b3e20
             have r₂ := b3e200 y
             grind)
          | exact resolve b3e20 b3e200
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e200
        have b3e275 : False := by grind
        exact b3e275
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b4e33 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) x)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e33 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e33
            | exact resolve b4e33 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e43 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b4e41 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e41
            | exact resolve b4e41 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e49 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
          have b4e51 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b4e17 x X0
               have i₂ := b4e43 x
               grind)
            | exact superpose b4e43 b4e17
            | (have j0 := b4e17 x X0
               grind)
            | (have r₁ := b4e17 x x
               have r₂ := b4e43 x
               grind)
            | exact resolve b4e17 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e52 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op x X0) = (k x X0) := by
            intro X0
            first
            | (have j0 := b4e51 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51
          have b4e54 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e49 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49
          have b4e249 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 x X0
               have i₂ := b4e54 (σ X0)
               grind)
            | exact superpose b4e54 b4e19
            | (have j1 := b4e54 (σ X0)
               grind)
            | exact resolve b4e19 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e8149 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e249 y
               grind)
            | exact superpose b4e249 b4e23
            | (have j1 := b4e249 y
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e249 y
               grind)
            | exact resolve b4e23 b4e249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e249
          have b4e8177 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
          clear b4e8149
          have b4e8195 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e8177
               grind)
            | exact superpose b4e8177 b4e20
            | exact resolve b4e20 b4e8177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8177
          have b4e8387 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e8195
               have i₂ := b4e52 y
               grind)
            | exact superpose b4e52 b4e8195
            | (have j1 := b4e52 y
               grind)
            | exact resolve b4e8195 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52 b4e8195
          have b4e8399 : y = (M.op y y) := by grind
          clear b4e8387
          have b4e8402 : False := by grind
          exact b4e8402
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
          have b5e69 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
          have b5e74 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b5e69 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e204 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e34 (σ x)
               have i₂ := b5e74 (σ x)
               grind)
            | exact superpose b5e74 b5e34
            | (have j1 := b5e74 (σ x)
               grind)
            | exact resolve b5e34 b5e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e74
          have b5e207 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e204
          have b5e211 : False := by grind
          exact b5e211
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b6e65 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e32 X0
             have i₂ := b6e17 X0 y
             grind)
          | exact superpose b6e17 b6e32
          | (have j1 := b6e17 y y
             grind)
          | exact resolve b6e32 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e72 : ∀ X0 : G, (M.op y X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e65 X0
             grind)
          | (have r₁ := b6e65 y
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e65 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e65 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e1600 : y ≠ y ∨ y = (M.op y y) := by
          first
          | (have j0 := b6e72 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e1601 : y = (M.op y y) := by grind
        clear b6e1600
        have b6e1607 : False := by grind
        exact b6e1607
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b7e37 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ x)) (σ x))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ x) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e43 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e37 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e37
            | exact resolve b7e37 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e44 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e43 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e43
            | exact resolve b7e43 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e45 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e17 (σ x) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) X0
               grind)
            | (have r₁ := b7e17 (σ x) x
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e48 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b7e45 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e162 : (σ x) = (M.op (σ x) x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e34 (σ x)
               have i₂ := b7e48 x
               grind)
            | exact superpose b7e48 b7e34
            | (have j1 := b7e48 x
               grind)
            | exact resolve b7e34 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e48
          have b7e171 : (σ x) = (M.op (σ x) x) := by
            first
            | (have r₁ := b7e162
               have r₂ := b7e22
               grind)
            | exact resolve b7e162 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e162
          have b7e175 : ∀ X0 : G, (M.op X0 (M.op (M.op x (σ x)) (σ x))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x (σ x)
               have i₂ := b7e171
               grind)
            | exact superpose b7e171 b7e13
            | exact resolve b7e13 b7e171
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e171
          have b7e176 : ∀ X0 : G, (M.op X0 (M.op x (σ x))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e175 X0
               have i₂ := b7e44 (M.op x (σ x))
               grind)
            | exact superpose b7e44 b7e175
            | exact resolve b7e175 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e175
          have b7e179 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b7e176 X0
               have i₂ := b7e44 x
               grind)
            | exact superpose b7e44 b7e176
            | exact resolve b7e176 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44 b7e176
          have b7e204 : x ≠ x := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e179 x
               grind)
            | exact superpose b7e179 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e179 x
               grind)
            | exact resolve b7e22 b7e179
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e179
          have b7e205 : False := by grind
          exact b7e205
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
          have b8e55 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
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
          have b8e61 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e55 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e162 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 y X0
               have i₂ := b8e61 (σ X0)
               grind)
            | exact superpose b8e61 b8e19
            | (have j1 := b8e61 (σ X0)
               grind)
            | exact resolve b8e19 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e6367 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e162 x
               grind)
            | exact superpose b8e162 b8e20
            | (have j1 := b8e162 x
               grind)
            | exact resolve b8e20 b8e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e162
          have b8e6474 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e6367
               have r₂ := b8e24
               grind)
            | exact resolve b8e6367 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6367
          have b8e6484 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e6474
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e6474
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e6474 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6474
          have b8e6502 : x = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e6484
          have b8e6509 : y = (M.op y y) := by
            first
            | (have r₁ := b8e6502
               have r₂ := b8e22
               grind)
            | exact resolve b8e6502 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6502
          have b8e6510 : False := by grind
          exact b8e6510

/-- `Equation108`: `x = x ◇ ((y ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_pxy_pyx_Equation108 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law108 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law108.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
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
    · have b0e11 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) X1)) = X0 := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e27 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e22 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e22
        | exact resolve b0e22 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e28 : ∀ X0 : G, (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e21 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e21
        | exact resolve b0e21 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21
      have b0e37 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e27 (σ x)
           grind)
        | exact superpose b0e27 b0e18
        | exact resolve b0e18 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27
      have b0e38 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e37
           have i₂ := b0e28 x
           grind)
        | exact superpose b0e28 b0e37
        | exact resolve b0e37 b0e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28 b0e37
      have b0e39 : False := by grind
      exact b0e39
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) X1)) = X0 := by
          intro X0 X1
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
        have b1e23 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e23 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e23
          | exact resolve b1e23 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e48 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 y
             have i₂ := b1e30 y
             grind)
          | exact superpose b1e30 b1e15
          | (have j0 := b1e15 X0 y
             grind)
          | (have r₁ := b1e15 X0 y
             have r₂ := b1e30 y
             grind)
          | exact resolve b1e15 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e48 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e62 : (σ y) ≠ (k (σ y) y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e51 (σ y)
             grind)
          | exact superpose b1e51 b1e21
          | exact resolve b1e21 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e89 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e17 (σ X1) (σ X0)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X0) (σ X0)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e99 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) y) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e89 X0 X1
             have i₂ := b1e51 (σ X0)
             grind)
          | exact superpose b1e51 b1e89
          | (have j0 := b1e89 X0 X1
             grind)
          | exact resolve b1e89 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e89
        have b1e101 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (k (σ X0) y) ∨ (σ X1) = (k (σ X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b1e99 X0 X1
             have i₂ := b1e51 (σ X1)
             grind)
          | exact superpose b1e51 b1e99
          | (have j0 := b1e99 X0 X1
             grind)
          | exact resolve b1e99 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e99
        have b1e1294 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e101 y y
             grind)
          | exact superpose b1e101 b1e21
          | (have j1 := b1e101 y y
             grind)
          | exact resolve b1e21 b1e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e101
        have b1e1350 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) := by grind
        clear b1e1294
        have b1e1381 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b1e1350
             have r₂ := b1e62
             grind)
          | exact resolve b1e1350 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62 b1e1350
        have b1e1404 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e1381
             have i₂ := b1e51 y
             grind)
          | exact superpose b1e51 b1e1381
          | exact resolve b1e1381 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e1381
        have b1e1414 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e1404
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1404
          | exact resolve b1e1404 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1404
        have b1e1415 : False := by grind
        exact b1e1415
      · have b2e12 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) X1)) = X0 := by
          intro X0 X1
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
        have b2e23 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e23 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e23
          | exact resolve b2e23 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23
        have b2e33 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e37 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b2e15 X0 y
             have i₂ := b2e28 y
             grind)
          | exact superpose b2e28 b2e15
          | (have j0 := b2e15 X0 y
             grind)
          | (have r₁ := b2e15 X0 y
             have r₂ := b2e28 y
             grind)
          | exact resolve b2e15 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e38 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b2e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e45 : (σ y) ≠ (k (σ y) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e38 (σ y)
             grind)
          | exact superpose b2e38 b2e21
          | exact resolve b2e21 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X0 X2
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X0
             have j1 := b2e17 X2 X2
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e70 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e17 (σ X1) (σ X0)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X0) (σ X0)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e74 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e66 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e80 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) y) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e70 X0 X1
             have i₂ := b2e38 (σ X0)
             grind)
          | exact superpose b2e38 b2e70
          | (have j0 := b2e70 X0 X1
             grind)
          | exact resolve b2e70 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (k (σ X0) y) ∨ (σ X1) = (k (σ X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b2e80 X0 X1
             have i₂ := b2e38 (σ X1)
             grind)
          | exact superpose b2e38 b2e80
          | (have j0 := b2e80 X0 X1
             grind)
          | exact resolve b2e80 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e80
        have b2e799 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e74 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e74
        have b2e800 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e799 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e799
        have b2e808 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e800 X0
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e800 x
             have r₂ := b2e15 X0 x
             grind)
          | exact resolve b2e800 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e800
        have b2e846 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e33 X0 (τ X0)
             have i₂ := b2e808 (τ X0)
             grind)
          | exact superpose b2e808 b2e33
          | exact resolve b2e33 b2e808
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e847 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e846 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e846
          | exact resolve b2e846 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e846
        have b2e855 : ∀ X0 : G, (k X0 X0) = (σ (k (τ X0) y)) := by
          intro X0
          first
          | (have i₁ := b2e847 X0
             have i₂ := b2e38 (τ X0)
             grind)
          | exact superpose b2e38 b2e847
          | exact resolve b2e847 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e847
        have b2e863 : ∀ X0 : G, (k X0 (σ y)) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b2e855 X0
             have i₂ := b2e33 X0 y
             grind)
          | exact superpose b2e33 b2e855
          | exact resolve b2e855 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33 b2e855
        have b2e1071 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e863 (σ X0)
             grind)
          | (have i₁ := b2e18 X0 y
             have i₂ := b2e863 (σ X0)
             grind)
          | exact superpose b2e863 b2e18
          | exact resolve b2e18 b2e863
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e863
        have b2e1082 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e1071 X0
             have i₂ := b2e808 X0
             grind)
          | exact superpose b2e808 b2e1071
          | exact resolve b2e1071 b2e808
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e808 b2e1071
        have b2e1111 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e1082 X0
             have i₂ := b2e18 X0 y
             grind)
          | exact superpose b2e18 b2e1082
          | exact resolve b2e1082 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1082
        have b2e2035 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) ∨ (σ y) = (k (σ y) y) := by
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
        have b2e2099 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) := by grind
        clear b2e2035
        have b2e2136 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b2e2099
             have r₂ := b2e45
             grind)
          | exact resolve b2e2099 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45 b2e2099
        have b2e2162 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e2136
             have i₂ := b2e1111 y
             grind)
          | exact superpose b2e1111 b2e2136
          | exact resolve b2e2136 b2e1111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1111 b2e2136
        have b2e2171 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e2162
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e2162
          | exact resolve b2e2162 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2162
        have b2e2172 : False := by grind
        exact b2e2172
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) X1)) = X0 := by
          intro X0 X1
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e21 : x = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e24 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e29 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e24 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e24
          | exact resolve b3e24 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e30 : ∀ X0 : G, (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b3e23 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e23
          | exact resolve b3e23 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23
        have b3e45 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b3e15 X0 x
             have i₂ := b3e30 x
             grind)
          | exact superpose b3e30 b3e15
          | (have j0 := b3e15 X0 x
             grind)
          | (have r₁ := b3e15 X0 x
             have r₂ := b3e30 x
             grind)
          | exact resolve b3e15 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e46 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e15 X0 (σ y)
             have i₂ := b3e29 (σ y)
             grind)
          | exact superpose b3e29 b3e15
          | (have j0 := b3e15 X0 (σ y)
             grind)
          | (have r₁ := b3e15 X0 (σ y)
             have r₂ := b3e29 (σ y)
             grind)
          | exact resolve b3e15 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e46 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b3e45 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e59 : (σ y) = (k (σ y) x) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e48 (σ y)
             grind)
          | exact superpose b3e48 b3e22
          | exact resolve b3e22 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e81 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e15 X1 X0
             have i₂ := b3e17 X0 X2
             grind)
          | exact superpose b3e17 b3e15
          | (have j0 := b3e15 X1 X0
             have j1 := b3e17 X2 X2
             grind)
          | (have r₁ := b3e15 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X0 X0
             have r₂ := b3e17 X0 X1
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e85 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e81 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81
        have b3e106 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e47 (σ X0)
             grind)
          | exact superpose b3e47 b3e18
          | exact resolve b3e18 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e108 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e106 X0
             have i₂ := b3e48 (σ X0)
             grind)
          | exact superpose b3e48 b3e106
          | exact resolve b3e106 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e106
        have b3e468 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e59
             have i₂ := b3e108 y
             grind)
          | exact superpose b3e108 b3e59
          | exact resolve b3e59 b3e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59 b3e108
        have b3e558 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e85 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85
        have b3e559 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e558 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e558
        have b3e563 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e559 X0
             have j1 := b3e15 X0 X0
             grind)
          | (have r₁ := b3e559 x
             have r₂ := b3e15 X0 x
             grind)
          | exact resolve b3e559 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e559
        have b3e733 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e468
             grind)
          | exact superpose b3e468 b3e13
          | exact resolve b3e13 b3e468
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e468
        have b3e735 : y = (k y y) := by
          first
          | (have i₁ := b3e733
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e733
          | exact resolve b3e733 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e733
        have b3e742 : y = (M.op y y) := by
          first
          | (have i₁ := b3e735
             have i₂ := b3e563 y
             grind)
          | exact superpose b3e563 b3e735
          | exact resolve b3e735 b3e563
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e563 b3e735
        have b3e745 : False := by grind
        exact b3e745
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) X1)) = X0 := by
            intro X0 X1
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e31 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e26 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e26
            | exact resolve b4e26 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e32 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b4e25 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e25
            | exact resolve b4e25 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e34 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e46 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b4e16 X0 x
               have i₂ := b4e32 x
               grind)
            | exact superpose b4e32 b4e16
            | (have j0 := b4e16 X0 x
               grind)
            | (have r₁ := b4e16 X0 x
               have r₂ := b4e32 x
               grind)
            | exact resolve b4e16 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e47 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e16 X0 (σ x)
               have i₂ := b4e31 (σ x)
               grind)
            | exact superpose b4e31 b4e16
            | (have j0 := b4e16 X0 (σ x)
               grind)
            | (have r₁ := b4e16 X0 (σ x)
               have r₂ := b4e31 (σ x)
               grind)
            | exact resolve b4e16 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b4e47 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47
          have b4e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b4e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e66 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e17 (σ x) X0
               have i₂ := b4e31 (σ x)
               grind)
            | exact superpose b4e31 b4e17
            | (have j0 := b4e17 (σ x) X0
               grind)
            | (have r₁ := b4e17 (σ x) x
               have r₂ := b4e31 (σ x)
               grind)
            | exact resolve b4e17 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e67 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e17 x X0
               have i₂ := b4e32 x
               grind)
            | exact superpose b4e32 b4e17
            | (have j0 := b4e17 x X0
               grind)
            | (have r₁ := b4e17 x x
               have r₂ := b4e32 x
               grind)
            | exact resolve b4e17 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e68 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b4e67 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67
          have b4e69 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e66 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66
          have b4e82 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18 X0 X2
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e18 X1 X1
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e84 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e18 X0 X2
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X1 X0
               have j1 := b4e18 X2 X2
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e90 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e84 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84
          have b4e91 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e82 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e82
          have b4e118 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 x
               have i₂ := b4e48 (σ X0)
               grind)
            | exact superpose b4e48 b4e19
            | exact resolve b4e19 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e122 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e118 X0
               have i₂ := b4e49 (σ X0)
               grind)
            | exact superpose b4e49 b4e118
            | exact resolve b4e118 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e118
          have b4e139 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e34 X1 X0
               grind)
            | exact superpose b4e34 b4e14
            | exact resolve b4e14 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e625 : ∀ X0 X1 : G, (σ y) ≠ (k (σ y) X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e23
               have i₂ := b4e90 X0 (σ y) X1
               grind)
            | exact superpose b4e90 b4e23
            | (have j1 := b4e90 X0 X1 X1
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e90 X0 X1 (σ y)
               grind)
            | exact resolve b4e23 b4e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90
          have b4e1181 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k (σ X0) X2) = (M.op X2 (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e91 (σ X0) (σ X1) X2
               grind)
            | exact superpose b4e91 b4e19
            | (have j1 := b4e91 (σ X0) (σ X1) X2
               grind)
            | exact resolve b4e19 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91
          have b4e1252 : ∀ X0 X1 X2 : G, (σ X1) = (k (σ X1) x) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k (σ X0) X2) = (M.op X2 (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e1181 X0 X1 X2
               have i₂ := b4e49 (σ X1)
               grind)
            | exact superpose b4e49 b4e1181
            | (have j0 := b4e1181 X0 X1 X2
               grind)
            | exact resolve b4e1181 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49 b4e1181
          have b4e1270 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) X2) = (M.op X2 (σ X0)) ∨ (M.op X2 X2) = X2 ∨ (σ X1) = (σ (k X1 x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e1252 X0 X1 X2
               have i₂ := b4e122 X1
               grind)
            | exact superpose b4e122 b4e1252
            | (have j0 := b4e1252 X0 X1 X2
               grind)
            | exact resolve b4e1252 b4e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e122 b4e1252
          have b4e1819 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (k x X0) = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0
               have i₂ := b4e68 X0
               grind)
            | exact superpose b4e68 b4e13
            | (have j1 := b4e68 X0
               grind)
            | exact resolve b4e13 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1820 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k x X0) = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e68 X0
               grind)
            | exact superpose b4e68 b4e16
            | (have j0 := b4e16 X1 X0
               have j1 := b4e68 X0
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e68 X0
               grind)
            | exact resolve b4e16 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1850 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k x X0) = (M.op x X0) := by
            intro X0 X1
            first
            | (have j0 := b4e1820 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1820
          have b4e8268 : ∀ X0 X1 : G, (σ y) ≠ (σ (k y X0)) ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e625 (σ X0) X1
               have i₂ := b4e19 y X0
               grind)
            | exact superpose b4e19 b4e625
            | (have j0 := b4e625 (σ X0) X1
               grind)
            | exact resolve b4e625 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e625
          have b4e125653 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k x X0) = (M.op x X0) ∨ (k x X0) = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e1819 X0 X1
               have i₂ := b4e68 X0
               grind)
            | exact superpose b4e68 b4e1819
            | (have j0 := b4e1819 X0 X1
               have j1 := b4e68 X0
               grind)
            | exact resolve b4e1819 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68 b4e1819
          have b4e125820 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k x X0) = (M.op x X0) := by
            intro X0 X1
            first
            | (have j0 := b4e125653 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e125653
          have b4e129278 : ∀ X0 : G, (M.op x x) ≠ (M.op x X0) ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b4e1850 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1850
          have b4e129287 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e129278 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e129278
            | (have j0 := b4e129278 X0
               grind)
            | exact resolve b4e129278 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129278
          have b4e129392 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b4e129287 X0
               have j1 := b4e125820 X0 x
               grind)
            | (have r₁ := b4e129287 X0
               have r₂ := b4e125820 X0 x
               grind)
            | exact resolve b4e129287 b4e125820
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e125820 b4e129287
          have b4e228496 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (M.op X0 X0) = X0 ∨ (σ y) = (σ (k y x)) := by
            intro X0
            first
            | (have i₁ := b4e20
               have i₂ := b4e1270 x y X0
               grind)
            | exact superpose b4e1270 b4e20
            | (have j1 := b4e1270 x y X0
               grind)
            | exact resolve b4e20 b4e1270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1270
          have b4e229136 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e228496 X0
               have j1 := b4e8268 x X0
               grind)
            | (have r₁ := b4e228496 X0
               have r₂ := b4e8268 x x
               grind)
            | exact resolve b4e228496 b4e8268
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8268 b4e228496
          have b4e229144 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e229136 X0
               have i₂ := b4e129392 y
               grind)
            | exact superpose b4e129392 b4e229136
            | (have j0 := b4e229136 X0
               grind)
            | exact resolve b4e229136 b4e129392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e229136
          have b4e229145 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e229144 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e229144
          have b4e229148 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e229145 X0
               have i₂ := b4e31 X0
               grind)
            | exact superpose b4e31 b4e229145
            | (have j0 := b4e229145 X0
               grind)
            | exact resolve b4e229145 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e229145
          have b4e229214 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e69 X0
               have i₂ := b4e229148 X0
               grind)
            | exact superpose b4e229148 b4e69
            | (have j0 := b4e69 X0
               have j1 := b4e229148 X0
               grind)
            | exact resolve b4e69 b4e229148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e229217 : ∀ X0 : G, (τ X0) = (k x (τ X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e139 x X0
               have i₂ := b4e229148 X0
               grind)
            | exact superpose b4e229148 b4e139
            | (have j1 := b4e229148 X0
               grind)
            | exact resolve b4e139 b4e229148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e139 b4e229148
          have b4e229416 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e229214 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e229214
          have b4e229484 : ∀ X0 : G, (τ X0) = (M.op x (τ X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e229217 X0
               have i₂ := b4e129392 (τ X0)
               grind)
            | exact superpose b4e129392 b4e229217
            | (have j0 := b4e229217 X0
               grind)
            | exact resolve b4e229217 b4e129392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129392 b4e229217
          have b4e233452 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e229416 (σ y)
               grind)
            | exact superpose b4e229416 b4e23
            | (have j1 := b4e229416 (σ y)
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e229416 (σ y)
               grind)
            | exact resolve b4e23 b4e229416
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e229416
          have b4e233458 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b4e233452
          have b4e234707 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e233458
               grind)
            | exact superpose b4e233458 b4e20
            | exact resolve b4e20 b4e233458
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e233458
          have b4e239464 : (σ y) ≠ (σ y) ∨ (τ (σ y)) = (M.op x (τ (σ y))) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e229484 (σ y)
               grind)
            | exact superpose b4e229484 b4e23
            | (have j1 := b4e229484 (σ y)
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e229484 (σ y)
               grind)
            | exact resolve b4e23 b4e229484
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e229484
          have b4e239466 : (τ (σ y)) = (M.op x (τ (σ y))) := by grind
          clear b4e239464
          have b4e239471 : y = (M.op x y) := by
            first
            | (have i₁ := b4e239466
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e239466
            | exact resolve b4e239466 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e239466
          have b4e241166 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e234707
               have i₂ := b4e239471
               grind)
            | exact superpose b4e239471 b4e234707
            | exact resolve b4e234707 b4e239471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e234707 b4e239471
          have b4e241168 : False := by grind
          exact b4e241168
        · have b5e13 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) X1)) = X0 := by
            intro X0 X1
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b5e25 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e25 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e25
            | exact resolve b5e25 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25
          have b5e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e43 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b5e16 X0 x
               have i₂ := b5e30 x
               grind)
            | exact superpose b5e30 b5e16
            | (have j0 := b5e16 X0 x
               grind)
            | (have r₁ := b5e16 X0 x
               have r₂ := b5e30 x
               grind)
            | exact resolve b5e16 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b5e43 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e52 : (σ x) ≠ (k (σ x) x) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e44 (σ x)
               grind)
            | exact superpose b5e44 b5e24
            | exact resolve b5e24 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e72 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 X1 X0
               have i₂ := b5e18 X0 X2
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X1 X0
               have j1 := b5e18 X2 X2
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X0 X0
               have r₂ := b5e18 X0 X1
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e76 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e18 (σ X1) (σ X0)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X0) (σ X0)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e81 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e72 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72
          have b5e88 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) x) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e76 X0 X1
               have i₂ := b5e44 (σ X0)
               grind)
            | exact superpose b5e44 b5e76
            | (have j0 := b5e76 X0 X1
               grind)
            | exact resolve b5e76 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76
          have b5e90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (k (σ X0) x) ∨ (σ X1) = (k (σ X1) x) := by
            intro X0 X1
            first
            | (have i₁ := b5e88 X0 X1
               have i₂ := b5e44 (σ X1)
               grind)
            | exact superpose b5e44 b5e88
            | (have j0 := b5e88 X0 X1
               grind)
            | exact resolve b5e88 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e88
          have b5e798 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e81 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e799 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e798 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e798
          have b5e807 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e799 X0
               have j1 := b5e16 X0 X0
               grind)
            | (have r₁ := b5e799 x
               have r₂ := b5e16 X0 x
               grind)
            | exact resolve b5e799 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e799
          have b5e845 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e31 X0 (τ X0)
               have i₂ := b5e807 (τ X0)
               grind)
            | exact superpose b5e807 b5e31
            | exact resolve b5e31 b5e807
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e846 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e845 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e845
            | exact resolve b5e845 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e845
          have b5e854 : ∀ X0 : G, (σ (k (τ X0) x)) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e846 X0
               have i₂ := b5e44 (τ X0)
               grind)
            | exact superpose b5e44 b5e846
            | exact resolve b5e846 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e846
          have b5e862 : ∀ X0 : G, (k X0 (σ x)) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e854 X0
               have i₂ := b5e31 X0 x
               grind)
            | exact superpose b5e31 b5e854
            | exact resolve b5e854 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e854
          have b5e1066 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e862 (σ X0)
               grind)
            | (have i₁ := b5e19 X0 x
               have i₂ := b5e862 (σ X0)
               grind)
            | exact superpose b5e862 b5e19
            | exact resolve b5e19 b5e862
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e862
          have b5e1077 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e1066 X0
               have i₂ := b5e807 X0
               grind)
            | exact superpose b5e807 b5e1066
            | exact resolve b5e1066 b5e807
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e807 b5e1066
          have b5e1106 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e1077 X0
               have i₂ := b5e19 X0 x
               grind)
            | exact superpose b5e19 b5e1077
            | exact resolve b5e1077 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1077
          have b5e2031 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (k (σ x) x) ∨ (σ x) = (k (σ x) x) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e90 x x
               grind)
            | exact superpose b5e90 b5e24
            | (have j1 := b5e90 x x
               grind)
            | exact resolve b5e24 b5e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90
          have b5e2093 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (k (σ x) x) := by grind
          clear b5e2031
          have b5e2130 : (σ x) ≠ (σ (k x x)) := by
            first
            | (have r₁ := b5e2093
               have r₂ := b5e52
               grind)
            | exact resolve b5e2093 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52 b5e2093
          have b5e2156 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e2130
               have i₂ := b5e1106 x
               grind)
            | exact superpose b5e1106 b5e2130
            | exact resolve b5e2130 b5e1106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1106 b5e2130
          have b5e2166 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e2156
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2156
            | exact resolve b5e2156 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2156
          have b5e2167 : False := by grind
          exact b5e2167
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) X1)) = X0 := by
          intro X0 X1
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
        have b6e23 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e28 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e23 X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e23
          | exact resolve b6e23 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e33 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b6e38 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e15 X0 (σ y)
             have i₂ := b6e28 (σ y)
             grind)
          | exact superpose b6e28 b6e15
          | (have j0 := b6e15 X0 (σ y)
             grind)
          | (have r₁ := b6e15 X0 (σ y)
             have r₂ := b6e28 (σ y)
             grind)
          | exact resolve b6e15 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e39 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e38 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e82 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k (τ X0) X1)
             have i₂ := b6e33 X0 X1
             grind)
          | exact superpose b6e33 b6e13
          | exact resolve b6e13 b6e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e96 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e82 X0 y
             have i₂ := b6e39 X0
             grind)
          | exact superpose b6e39 b6e82
          | exact resolve b6e82 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39 b6e82
        have b6e144 : (τ (σ y)) = (k (τ (σ y)) y) := by
          first
          | (have i₁ := b6e96 (σ y)
             have i₂ := b6e28 (σ y)
             grind)
          | exact superpose b6e28 b6e96
          | exact resolve b6e96 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28 b6e96
        have b6e154 : y = (k y y) := by
          first
          | (have i₁ := b6e144
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e144
          | exact resolve b6e144 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e144
        have b6e224 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e154
             grind)
          | exact superpose b6e154 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e154
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e154
        have b6e225 : y = (M.op y y) := by grind
        clear b6e224
        have b6e227 : False := by grind
        exact b6e227
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) X1)) = X0 := by
            intro X0 X1
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b7e25 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e25 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e25
            | exact resolve b7e25 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25
          have b7e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b7e40 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k (τ X0) X1)
               have i₂ := b7e31 X0 X1
               grind)
            | exact superpose b7e31 b7e14
            | exact resolve b7e14 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e43 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e16 X0 (σ x)
               have i₂ := b7e30 (σ x)
               grind)
            | exact superpose b7e30 b7e16
            | (have j0 := b7e16 X0 (σ x)
               grind)
            | (have r₁ := b7e16 X0 (σ x)
               have r₂ := b7e30 (σ x)
               grind)
            | exact resolve b7e16 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b7e43 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e101 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e40 X0 x
               have i₂ := b7e44 X0
               grind)
            | exact superpose b7e44 b7e40
            | exact resolve b7e40 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40 b7e44
          have b7e149 : (τ (σ x)) = (k (τ (σ x)) x) := by
            first
            | (have i₁ := b7e101 (σ x)
               have i₂ := b7e30 (σ x)
               grind)
            | exact superpose b7e30 b7e101
            | exact resolve b7e101 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e101
          have b7e159 : x = (k x x) := by
            first
            | (have i₁ := b7e149
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e149
            | exact resolve b7e149 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e149
          have b7e185 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x x
               have i₂ := b7e159
               grind)
            | exact superpose b7e159 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e159
          have b7e186 : x = (M.op x x) := by grind
          clear b7e185
          have b7e188 : False := by grind
          exact b7e188
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
          have b8e56 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
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
          have b8e62 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e56 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e145 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 y X0
               have i₂ := b8e62 (σ X0)
               grind)
            | exact superpose b8e62 b8e19
            | (have j1 := b8e62 (σ X0)
               grind)
            | exact resolve b8e19 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e10611 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e145 x
               grind)
            | exact superpose b8e145 b8e20
            | (have j1 := b8e145 x
               grind)
            | exact resolve b8e20 b8e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e145
          have b8e10823 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e10611
               have r₂ := b8e24
               grind)
            | exact resolve b8e10611 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10611
          have b8e10929 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e10823
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e10823
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e10823 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10823
          have b8e10942 : x = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e10929
          have b8e10949 : y = (M.op y y) := by
            first
            | (have r₁ := b8e10942
               have r₂ := b8e22
               grind)
            | exact resolve b8e10942 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10942
          have b8e10950 : False := by grind
          exact b8e10950

/-- `Equation111`: `x = x ◇ ((y ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_x_pyx_Equation111 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law111 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law111.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = a :=
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
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = y := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        grind
      have b0e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        grind
      clear b0e33
      have b0e86 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e34
      have b0e92 : False := by grind
      exact b0e92
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) X1)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e28 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0 (M.op (M.op x x) x)
               have i₂ := b4e13 X0 x x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e39
          have b4e72 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e18 (σ X1) (σ X0)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X1) (M.op (σ X1) (σ X1))
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e77 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e72 X0 X1
               have i₂ := b4e40 X1
               grind)
            | exact superpose b4e40 b4e72
            | (have j0 := b4e72 X0 X1
               grind)
            | exact resolve b4e72 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72
          have b4e155 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e28 (σ X0) X1
               have i₂ := b4e40 X0
               grind)
            | exact superpose b4e40 b4e28
            | exact resolve b4e28 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e356 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e77 x y
               grind)
            | exact superpose b4e77 b4e20
            | (have j1 := b4e77 (M.op y y) y
               grind)
            | exact resolve b4e20 b4e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77
          have b4e376 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have r₁ := b4e356
               have r₂ := b4e23
               grind)
            | exact resolve b4e356 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e356
          have b4e1854 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b4e376
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e376
            | (have j1 := b4e18 y (M.op y y)
               grind)
            | (have r₁ := b4e376
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e376
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e376 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e376
          have b4e1855 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = y := by grind
          clear b4e1854
          have b4e1858 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have r₁ := b4e1855
               have r₂ := b4e21
               grind)
            | exact resolve b4e1855 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1855
          have b4e12831 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e14 (M.op y y)
               have i₂ := b4e1858
               grind)
            | exact superpose b4e1858 b4e14
            | exact resolve b4e14 b4e1858
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1858
          have b4e12897 : y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e12831
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e12831
            | exact resolve b4e12831 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12831
          have b4e12898 : y = (M.op y y) := by grind
          clear b4e12897
          have b4e12900 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e28 y X0
               have i₂ := b4e12898
               grind)
            | exact superpose b4e12898 b4e28
            | exact resolve b4e28 b4e12898
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28
          have b4e12906 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e155 y X0
               have i₂ := b4e12898
               grind)
            | exact superpose b4e12898 b4e155
            | exact resolve b4e155 b4e12898
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e155 b4e12898
          have b4e13668 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e12906 (σ x)
               grind)
            | exact superpose b4e12906 b4e20
            | exact resolve b4e20 b4e12906
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12906
          have b4e13707 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e13668
               have i₂ := b4e12900 x
               grind)
            | exact superpose b4e12900 b4e13668
            | exact resolve b4e13668 b4e12900
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12900 b4e13668
          have b4e13708 : False := by grind
          exact b4e13708
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op x x) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e38 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e37
          have b5e141 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e38 x
               grind)
            | exact superpose b5e38 b5e24
            | exact resolve b5e24 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e147 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e141
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e141
            | exact resolve b5e141 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e141
          have b5e148 : False := by grind
          exact b5e148
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) X1)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x x) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e27 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X0 (M.op (M.op x x) x)
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e27 (σ x) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e27
            | exact resolve b7e27 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e38 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e37
          have b7e117 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e29 (σ x)
               have i₂ := b7e38 x
               grind)
            | exact superpose b7e38 b7e29
            | exact resolve b7e29 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29 b7e38
          have b7e156 : (M.op x x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e117
               grind)
            | exact superpose b7e117 b7e14
            | exact resolve b7e14 b7e117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e117
          have b7e157 : x = (M.op x x) := by
            first
            | (have i₁ := b7e156
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e156
            | exact resolve b7e156 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e156
          have b7e161 : False := by grind
          exact b7e161
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) X1)) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b8e26 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 X0 (M.op (M.op x x) x)
               have i₂ := b8e13 X0 x x
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e36 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e35
          have b8e73 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e83 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e73 X0 X1
               have i₂ := b8e36 X1
               grind)
            | exact superpose b8e36 b8e73
            | (have j0 := b8e73 X0 X1
               grind)
            | exact resolve b8e73 b8e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e94 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 (σ X0) X1
               have i₂ := b8e36 X0
               grind)
            | exact superpose b8e36 b8e26
            | exact resolve b8e26 b8e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36
          have b8e235 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e83 x y
               grind)
            | exact superpose b8e83 b8e20
            | (have j1 := b8e83 (M.op y y) y
               grind)
            | exact resolve b8e20 b8e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83
          have b8e253 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e235
               have r₂ := b8e23
               grind)
            | exact resolve b8e235 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e235
          have b8e1566 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e253
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e253
            | (have j1 := b8e18 y (M.op y y)
               grind)
            | (have r₁ := b8e253
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e253
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e253 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e253
          have b8e1567 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = y := by grind
          clear b8e1566
          have b8e1570 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have r₁ := b8e1567
               have r₂ := b8e21
               grind)
            | exact resolve b8e1567 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1567
          have b8e5990 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e14 (M.op y y)
               have i₂ := b8e1570
               grind)
            | exact superpose b8e1570 b8e14
            | exact resolve b8e14 b8e1570
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1570
          have b8e6033 : y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e5990
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e5990
            | exact resolve b8e5990 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5990
          have b8e6034 : y = (M.op y y) := by grind
          clear b8e6033
          have b8e6186 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e26 y X0
               have i₂ := b8e6034
               grind)
            | exact superpose b8e6034 b8e26
            | exact resolve b8e26 b8e6034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e6192 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b8e94 y X0
               have i₂ := b8e6034
               grind)
            | exact superpose b8e6034 b8e94
            | exact resolve b8e94 b8e6034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e94 b8e6034
          have b8e6738 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e6192 (σ x)
               grind)
            | exact superpose b8e6192 b8e20
            | exact resolve b8e20 b8e6192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6192
          have b8e6754 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e6738
               have i₂ := b8e6186 x
               grind)
            | exact superpose b8e6186 b8e6738
            | exact resolve b8e6738 b8e6186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6186 b8e6738
          have b8e6755 : False := by grind
          exact b8e6755
