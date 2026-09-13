import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3352 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3352 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e66 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        grind
      have b0e68 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        first
        | (have j0 := b0e66 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66
      have b0e110 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e68 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e68
        | exact resolve b0e68 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e111 : (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e68 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e68
        | exact resolve b0e68 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e114 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e110
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e110
        | exact resolve b0e110 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e110
      have b0e115 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e114
           have i₂ := b0e111
           grind)
        | exact superpose b0e111 b0e114
        | exact resolve b0e114 b0e111
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e111 b0e114
      have b0e116 : False := by grind
      exact b0e116
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e32 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b1e33 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e32
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e32
          | exact resolve b1e32 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e63 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b1e65 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b1e63 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63
        have b1e86 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e33
             grind)
          | exact superpose b1e33 b1e19
          | exact resolve b1e19 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e109 : (M.op x y) = (k y x) := by
          first
          | (have i₁ := b1e65 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e65
          | exact resolve b1e65 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e115 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e86
             have i₂ := b1e109
             grind)
          | exact superpose b1e109 b1e86
          | exact resolve b1e86 b1e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e86 b1e109
        have b1e117 : False := by grind
        exact b1e117
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e39 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          grind
        have b2e57 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b2e59 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e57 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e160 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e59 X0
             have i₂ := b2e39 X0 X1
             grind)
          | (have i₁ := b2e59 X0
             have i₂ := b2e39 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e39 b2e59
          | (have j1 := b2e39 X1 X0
             grind)
          | exact resolve b2e59 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e59
        have b2e175 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e160 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e160
        have b2e207 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e175 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e175
        have b2e229 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e207 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e207
        have b2e328 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e229 (σ X0)
             grind)
          | exact superpose b2e229 b2e18
          | exact resolve b2e18 b2e229
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e335 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e328 X0
             have i₂ := b2e229 X0
             grind)
          | exact superpose b2e229 b2e328
          | exact resolve b2e328 b2e229
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e229 b2e328
        have b2e551 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e335 x
             grind)
          | exact superpose b2e335 b2e21
          | exact resolve b2e21 b2e335
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e335
        have b2e574 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e551
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e551
          | exact resolve b2e551 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e551
        have b2e575 : False := by grind
        exact b2e575
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e31 : (M.op x y) = (k y x) := by grind
        have b3e54 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b3e67 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e54
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e54
          | exact resolve b3e54 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e68 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e67
             have i₂ := b3e31
             grind)
          | exact superpose b3e31 b3e67
          | exact resolve b3e67 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67
        have b3e69 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have r₁ := b3e68
             have r₂ := b3e19
             grind)
          | exact resolve b3e68 b3e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e77 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b3e69
        have b3e79 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e77
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e77
          | exact resolve b3e77 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e77
        have b3e80 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e79
             have i₂ := b3e31
             grind)
          | exact superpose b3e31 b3e79
          | exact resolve b3e79 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31 b3e79
        have b3e81 : False := by grind
        exact b3e81
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e37 : (M.op x y) = (k y x) := by grind
          have b4e38 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b4e40 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e38
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e38
            | exact resolve b4e38 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e41 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e40
               have i₂ := b4e37
               grind)
            | exact superpose b4e37 b4e40
            | exact resolve b4e40 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e40
          have b4e42 : False := by grind
          exact b4e42
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e49 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e65 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e67 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e65 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65
          have b5e236 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e67 X0
               have i₂ := b5e49 X0 X1
               grind)
            | (have i₁ := b5e67 X0
               have i₂ := b5e49 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e49 b5e67
            | (have j1 := b5e49 X1 X0
               grind)
            | exact resolve b5e67 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49 b5e67
          have b5e252 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e236 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e236
          have b5e322 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e252 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e252
          have b5e323 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e322 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e322
          have b5e423 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e323 (σ X0)
               grind)
            | exact superpose b5e323 b5e19
            | exact resolve b5e19 b5e323
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e430 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e423 X0
               have i₂ := b5e323 X0
               grind)
            | exact superpose b5e323 b5e423
            | exact resolve b5e423 b5e323
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e323 b5e423
          have b5e628 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e430 y
               grind)
            | exact superpose b5e430 b5e24
            | exact resolve b5e24 b5e430
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e430
          have b5e646 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e628
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e628
            | exact resolve b5e628 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e628
          have b5e647 : False := by grind
          exact b5e647
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e33 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        have b6e35 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e33
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e33
          | exact resolve b6e33 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          grind
        have b6e55 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b6e70 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b6e72 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b6e70 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e102 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e72 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e72
          | exact resolve b6e72 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e108 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b6e102
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e102
          | exact resolve b6e102 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e102
        have b6e109 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e108
             grind)
          | exact superpose b6e108 b6e19
          | exact resolve b6e19 b6e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e108
        have b6e152 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e72 X0
             have i₂ := b6e51 X0 X1
             grind)
          | (have i₁ := b6e72 X0
             have i₂ := b6e51 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e51 b6e72
          | (have j1 := b6e51 X1 X0
             grind)
          | exact resolve b6e72 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51 b6e72
        have b6e166 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e152 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e152
        have b6e245 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (k x y) := by
          first
          | (have i₁ := b6e109
             have i₂ := b6e55 x y
             grind)
          | exact superpose b6e55 b6e109
          | (have j1 := b6e55 x y
             grind)
          | exact resolve b6e109 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55 b6e109
        have b6e274 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
        clear b6e245
        have b6e283 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b6e274
             have r₂ := b6e20
             grind)
          | exact resolve b6e274 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e274
        have b6e835 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e59 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e59
          | exact resolve b6e59 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e1024 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e835
        have b6e1083 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e1024
             grind)
          | exact superpose b6e1024 b6e13
          | exact resolve b6e13 b6e1024
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1024
        have b6e1097 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1083
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1083
          | exact resolve b6e1083 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1083
        have b6e1279 : y = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e166 x x
             have i₂ := b6e1097
             grind)
          | exact superpose b6e1097 b6e166
          | exact resolve b6e166 b6e1097
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e166 b6e1097
        have b6e1280 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e1279
        have b6e1292 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e1280
             have r₂ := b6e20
             grind)
          | exact resolve b6e1280 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1280
        have b6e1494 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e1292
             grind)
          | exact superpose b6e1292 b6e19
          | exact resolve b6e19 b6e1292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1496 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e35
             have i₂ := b6e1292
             grind)
          | exact superpose b6e1292 b6e35
          | exact resolve b6e35 b6e1292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e1502 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e1292
             grind)
          | exact superpose b6e1292 b6e13
          | exact resolve b6e13 b6e1292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1519 : x = y := by
          first
          | (have i₁ := b6e1502
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e1502
          | exact resolve b6e1502 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1502
        have b6e1525 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e1496
             have i₂ := b6e283
             grind)
          | exact superpose b6e283 b6e1496
          | exact resolve b6e1496 b6e283
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e283 b6e1496
        have b6e1526 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e1494
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1494
          | exact resolve b6e1494 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1494
        have b6e1533 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b6e1525
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1525
          | exact resolve b6e1525 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1525
        have b6e1534 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e1526
             have i₂ := b6e1292
             grind)
          | exact superpose b6e1292 b6e1526
          | exact resolve b6e1526 b6e1292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1526
        have b6e1540 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b6e1533
             have i₂ := b6e1292
             grind)
          | exact superpose b6e1292 b6e1533
          | exact resolve b6e1533 b6e1292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1292 b6e1533
        have b6e1541 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e1534
             have i₂ := b6e1519
             grind)
          | exact superpose b6e1519 b6e1534
          | exact resolve b6e1534 b6e1519
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1534
        have b6e1542 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e1540
             have i₂ := b6e1519
             grind)
          | exact superpose b6e1519 b6e1540
          | exact resolve b6e1540 b6e1519
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1519 b6e1540
        have b6e1543 : False := by grind
        exact b6e1543
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e59 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e78 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b7e80 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b7e78 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e256 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e80 X0
               have i₂ := b7e59 X0 X1
               grind)
            | (have i₁ := b7e80 X0
               have i₂ := b7e59 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e59 b7e80
            | (have j1 := b7e59 X1 X0
               grind)
            | exact resolve b7e80 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59 b7e80
          have b7e273 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e256 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e256
          have b7e504 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e273 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e273
          have b7e505 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e504 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e504
          have b7e602 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e505 (σ X0)
               grind)
            | exact superpose b7e505 b7e19
            | exact resolve b7e19 b7e505
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e609 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e602 X0
               have i₂ := b7e505 X0
               grind)
            | exact superpose b7e505 b7e602
            | exact resolve b7e602 b7e505
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e505 b7e602
          have b7e909 : (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e609 y
               grind)
            | exact superpose b7e609 b7e24
            | exact resolve b7e24 b7e609
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e609
          have b7e1558 : (M.op y y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e909
               grind)
            | exact superpose b7e909 b7e14
            | exact resolve b7e14 b7e909
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e909
          have b7e1577 : x = (M.op y y) := by
            first
            | (have i₁ := b7e1558
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1558
            | exact resolve b7e1558 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1558
          have b7e1582 : False := by grind
          exact b7e1582
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e59 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
          have b8e250 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e59 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59
          have b8e251 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e250
               have r₂ := b8e24
               grind)
            | exact resolve b8e250 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e250
          have b8e252 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e251
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e251
            | exact resolve b8e251 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e251
          have b8e253 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e252
               grind)
            | exact superpose b8e252 b8e20
            | exact resolve b8e20 b8e252
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e252
          have b8e259 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e253
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e253
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e253 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e253
          have b8e260 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e259
          have b8e261 : x = (M.op y y) := by
            first
            | (have r₁ := b8e260
               have r₂ := b8e21
               grind)
            | exact resolve b8e260 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e260
          have b8e263 : False := by grind
          exact b8e263

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3352 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3352 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
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
        have b1e45 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e47 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e45
        have b1e48 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e47
             have r₂ := b1e23
             grind)
          | exact resolve b1e47 b1e23
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
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e49
          | exact resolve b1e49 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e49
        have b1e51 : False := by grind
        exact b1e51
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
        have b2e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e140 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e447 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e140 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e140
          | (have j0 := b2e140 x y
             grind)
          | exact resolve b2e140 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e140
        have b2e450 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e447
        have b2e453 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e450
             have r₂ := b2e22
             grind)
          | exact resolve b2e450 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e450
        have b2e457 : False := by grind
        exact b2e457
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
        have b3e40 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
        have b3e42 : x = y ∨ x = (k x y) := by grind
        clear b3e40
        have b3e43 : x = (k x y) := by
          first
          | (have r₁ := b3e42
             have r₂ := b3e23
             grind)
          | exact resolve b3e42 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e42
        have b3e46 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e43
             grind)
          | exact superpose b3e43 b3e29
          | exact resolve b3e29 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e43
        have b3e47 : False := by grind
        exact b3e47
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
          have b5e44 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e46 : x = y ∨ x = (k x y) := by grind
          clear b5e44
          have b5e47 : x = (k x y) := by
            first
            | (have r₁ := b5e46
               have r₂ := b5e25
               grind)
            | exact resolve b5e46 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e46
          have b5e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e123 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e477 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e123 x y
               have i₂ := b5e47
               grind)
            | exact superpose b5e47 b5e123
            | (have j0 := b5e123 x y
               grind)
            | exact resolve b5e123 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e123
          have b5e481 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e477
          have b5e484 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e481
               have r₂ := b5e24
               grind)
            | exact resolve b5e481 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e481
          have b5e488 : False := by grind
          exact b5e488
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
        have b6e46 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
        have b6e48 : y = (M.op x y) ∨ x = (M.op x y) := by grind
        clear b6e46
        have b6e51 : x = (M.op x y) := by
          first
          | (have r₁ := b6e48
             have r₂ := b6e21
             grind)
          | exact resolve b6e48 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48
        have b6e54 : False := by grind
        exact b6e54
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
          have b7e36 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e38 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e36
          have b7e39 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e38
               have r₂ := b7e25
               grind)
            | exact resolve b7e38 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e38
          have b7e40 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e39
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e39
            | exact resolve b7e39 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39
          have b7e43 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e40
               grind)
            | exact superpose b7e40 b7e14
            | exact resolve b7e14 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e44 : x = (k x y) := by
            first
            | (have i₁ := b7e43
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e43
            | exact resolve b7e43 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e54 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e44
               grind)
            | exact superpose b7e44 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e55 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b7e54
          have b7e57 : y = (M.op x y) := by
            first
            | (have r₁ := b7e55
               have r₂ := b7e21
               grind)
            | exact resolve b7e55 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e59 : False := by grind
          exact b7e59
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
          have b8e43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e107 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e43 x y
               grind)
            | exact superpose b8e43 b8e20
            | (have j1 := b8e43 x y
               grind)
            | exact resolve b8e20 b8e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e121 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e107
               have r₂ := b8e24
               grind)
            | exact resolve b8e107 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107
          have b8e124 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e121
               have r₂ := b8e23
               grind)
            | exact resolve b8e121 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121
          have b8e125 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e124
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e124
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e124 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e124
          have b8e126 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e125
          have b8e127 : x = (M.op x y) := by
            first
            | (have r₁ := b8e126
               have r₂ := b8e22
               grind)
            | exact resolve b8e126 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e126
          have b8e128 : False := by grind
          exact b8e128

/-- `Equation3475`: `x ◇ x = y ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation3475 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3475 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3475.models_iff G M).mp hM
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
      have b0e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e47 (σ X0)
           grind)
        | exact superpose b0e47 b0e17
        | exact resolve b0e17 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e59 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e54 X0
           have i₂ := b0e47 X0
           grind)
        | exact superpose b0e47 b0e54
        | exact resolve b0e54 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e54
      have b0e244 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e59 x
           grind)
        | exact superpose b0e59 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e59 x
           grind)
        | exact resolve b0e22 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e59
      have b0e255 : False := by grind
      exact b0e255
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1
          grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e42 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
          first
          | (have i₁ := b1e12 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e42
             have i₂ := b1e12 (σ x) (σ y)
             grind)
          | exact superpose b1e12 b1e42
          | exact resolve b1e42 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e44 : False := by grind
        exact b1e44
      · have b2e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
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
        have b2e51 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b2e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e56 : (k x y) = (M.op y y) := by grind
        clear b2e51
        have b2e58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e54 (σ X0)
             grind)
          | exact superpose b2e54 b2e18
          | exact resolve b2e18 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e58 X0
             have i₂ := b2e54 X0
             grind)
          | exact superpose b2e54 b2e58
          | exact resolve b2e58 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54 b2e58
        have b2e74 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e17 X0 X2
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e17 X1 X1
             have i₂ := b2e17 X1 X1
             grind)
          | exact superpose b2e17 b2e17
          | (have j0 := b2e17 X0 X2
             have j1 := b2e17 X0 X2
             grind)
          | exact resolve b2e17 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e91 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (M.op X0 X0) X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0
             have i₂ := b2e17 X1 X0
             grind)
          | (have i₁ := b2e12 X1 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e12
          | (have j1 := b2e17 X1 X0
             grind)
          | exact resolve b2e12 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e104 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e17 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e114 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e91 X0 X1
             have i₂ := b2e12 X0 X0
             grind)
          | exact superpose b2e12 b2e91
          | (have j0 := b2e91 X0 X1
             grind)
          | exact resolve b2e91 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91
        have b2e119 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e114 X0 X1
             have j1 := b2e104 X1 X0
             grind)
          | (have r₁ := b2e114 X0 X1
             have r₂ := b2e104 X0 X1
             grind)
          | (have r₁ := b2e114 X1 X0
             have r₂ := b2e104 X0 X1
             grind)
          | (have r₁ := b2e114 X1 X1
             have r₂ := b2e104 X1 X1
             grind)
          | exact resolve b2e114 b2e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e104 b2e114
        have b2e147 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e65 y
             grind)
          | exact superpose b2e65 b2e22
          | exact resolve b2e22 b2e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e232 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e65 X0
             have i₂ := b2e119 X1 (σ X0)
             grind)
          | (have i₁ := b2e65 X0
             have i₂ := b2e119 (σ X0) (σ X0)
             grind)
          | exact superpose b2e119 b2e65
          | (have j1 := b2e119 X1 (σ X0)
             grind)
          | exact resolve b2e65 b2e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e235 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e119 X1 X0
             grind)
          | (have i₁ := b2e15 X1 X1
             have i₂ := b2e119 X0 X1
             grind)
          | exact superpose b2e119 b2e15
          | (have j0 := b2e15 X0 X0
             have j1 := b2e119 X1 X0
             grind)
          | (have r₁ := b2e15 X1 X0
             have r₂ := b2e119 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e119 X0 X0
             grind)
          | exact resolve b2e15 b2e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e119
        have b2e243 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e235 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e235
        have b2e2055 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e243 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e243
        have b2e5113 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e23
             have i₂ := b2e74 (σ x) (σ y) X0
             grind)
          | (have i₁ := b2e23
             have i₂ := b2e74 (σ x) X0 (σ y)
             grind)
          | exact superpose b2e74 b2e23
          | (have j1 := b2e74 (σ x) (σ y) (σ y)
             grind)
          | exact resolve b2e23 b2e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e74
        have b2e5494 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b2e5113 X0
             have j1 := b2e2055 (σ x) (σ y)
             grind)
          | (have r₁ := b2e5113 X0
             have r₂ := b2e2055 (σ x) (σ y)
             grind)
          | (have r₁ := b2e5113 (σ x)
             have r₂ := b2e2055 (σ x) (σ x)
             grind)
          | (have r₁ := b2e5113 x
             have r₂ := b2e2055 (σ x) x
             grind)
          | exact resolve b2e5113 b2e2055
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5113
        have b2e5709 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b2e5494 X0
             have j1 := b2e2055 (σ x) (σ y)
             grind)
          | (have r₁ := b2e5494 (σ x)
             have r₂ := b2e2055 (σ x) (σ x)
             grind)
          | (have r₁ := b2e5494 x
             have r₂ := b2e2055 (σ x) x
             grind)
          | exact resolve b2e5494 b2e2055
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2055 b2e5494
        have b2e5863 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b2e5709 (σ y)
             have j1 := b2e232 x (σ y)
             grind)
          | (have r₁ := b2e5709 x
             have r₂ := b2e232 x x
             grind)
          | exact resolve b2e5709 b2e232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e232 b2e5709
        have b2e5918 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e5863 X0
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e5863
          | (have j0 := b2e5863 X0
             grind)
          | exact resolve b2e5863 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5863
        have b2e5926 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e5918 X0
             have i₂ := b2e56
             grind)
          | exact superpose b2e56 b2e5918
          | (have j0 := b2e5918 X0
             grind)
          | exact resolve b2e5918 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5918
        have b2e5932 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b2e5926 X0
             grind)
          | (have r₁ := b2e5926 X0
             have r₂ := b2e147
             grind)
          | exact resolve b2e5926 b2e147
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5926
        have b2e6667 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 x X0
             have i₂ := b2e5932 (σ X0)
             grind)
          | exact superpose b2e5932 b2e18
          | exact resolve b2e18 b2e5932
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5932
        have b2e8083 : (σ (M.op y y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b2e147
             have i₂ := b2e6667 y
             grind)
          | exact superpose b2e6667 b2e147
          | exact resolve b2e147 b2e6667
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e147 b2e6667
        have b2e8198 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e8083
             have i₂ := b2e56
             grind)
          | exact superpose b2e56 b2e8083
          | exact resolve b2e8083 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56 b2e8083
        have b2e8199 : False := by grind
        exact b2e8199
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : (M.op x y) = (M.op y y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e31 : (M.op x y) = (M.op y (M.op (M.op x y) y)) := by
          first
          | (have i₁ := b3e12 y y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b3e31
             have i₂ := b3e12 x y
             grind)
          | exact superpose b3e12 b3e31
          | exact resolve b3e31 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e35 : False := by grind
        exact b3e35
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1
            grind
          have b4e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b4e22 : (M.op x y) = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e32 : (M.op x y) = (M.op y (M.op (M.op x y) y)) := by
            first
            | (have i₁ := b4e13 y y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e32
               have i₂ := b4e13 x y
               grind)
            | exact superpose b4e13 b4e32
            | exact resolve b4e32 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e36 : False := by grind
          exact b4e36
        · have b5e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b5e22 : (M.op x y) = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e32 : (M.op x y) = (M.op y (M.op (M.op x y) y)) := by
            first
            | (have i₁ := b5e13 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b5e32
               have i₂ := b5e13 x y
               grind)
            | exact superpose b5e13 b5e32
            | exact resolve b5e32 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e36 : False := by grind
          exact b5e36
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
        have b6e53 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e55 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e53
        have b6e57 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e55
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e55
          | exact resolve b6e55 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e76 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e57
             grind)
          | exact superpose b6e57 b6e15
          | exact resolve b6e15 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e78 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e76
        have b6e79 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e78
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e78
          | exact resolve b6e78 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78
        have b6e80 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e79
             have i₂ := b6e54 y
             grind)
          | exact superpose b6e54 b6e79
          | exact resolve b6e79 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54 b6e79
        have b6e137 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e80
             grind)
          | exact superpose b6e80 b6e13
          | exact resolve b6e13 b6e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80
        have b6e138 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e137
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e137
          | exact resolve b6e137 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e137
        have b6e185 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e138
             grind)
          | exact superpose b6e138 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e138
        have b6e186 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
        clear b6e185
        have b6e188 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e186
             have r₂ := b6e21
             grind)
          | exact resolve b6e186 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e186
        have b6e190 : False := by grind
        exact b6e190
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1
            grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e50 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
            first
            | (have i₁ := b7e13 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e51 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e13 (σ x) (σ y)
               grind)
            | exact superpose b7e13 b7e50
            | exact resolve b7e50 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e52 : False := by grind
          exact b7e52
        · have b8e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e65 (σ X0)
               grind)
            | exact superpose b8e65 b8e19
            | exact resolve b8e19 b8e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e68 X0
               have i₂ := b8e65 X0
               grind)
            | exact superpose b8e65 b8e68
            | exact resolve b8e68 b8e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65 b8e68
          have b8e91 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e77 y
               grind)
            | exact superpose b8e77 b8e24
            | exact resolve b8e24 b8e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e119 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (M.op X0 X0) X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e13 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X1 X0
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e127 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
          have b8e133 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e140 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e127 X0 X1
               have i₂ := b8e77 X0
               grind)
            | exact superpose b8e77 b8e127
            | (have j0 := b8e127 X0 X1
               grind)
            | exact resolve b8e127 b8e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e127
          have b8e142 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e119 X0 X1
               have i₂ := b8e13 X0 X0
               grind)
            | exact superpose b8e13 b8e119
            | (have j0 := b8e119 X0 X1
               grind)
            | exact resolve b8e119 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e119
          have b8e146 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e140 X0 X1
               have i₂ := b8e77 X1
               grind)
            | exact superpose b8e77 b8e140
            | (have j0 := b8e140 X0 X1
               grind)
            | exact resolve b8e140 b8e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e140
          have b8e147 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e142 X0 X1
               have j1 := b8e133 X1 X0
               grind)
            | (have r₁ := b8e142 X0 X1
               have r₂ := b8e133 X0 X1
               grind)
            | (have r₁ := b8e142 X1 X0
               have r₂ := b8e133 X0 X1
               grind)
            | (have r₁ := b8e142 X1 X1
               have r₂ := b8e133 X1 X1
               grind)
            | exact resolve b8e142 b8e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e133 b8e142
          have b8e4520 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e146 x y
               grind)
            | exact superpose b8e146 b8e20
            | (have j1 := b8e146 x y
               grind)
            | exact resolve b8e20 b8e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e146
          have b8e4697 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e4520
               have r₂ := b8e91
               grind)
            | exact resolve b8e4520 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91 b8e4520
          have b8e15700 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e4697
               have i₂ := b8e147 y x
               grind)
            | exact superpose b8e147 b8e4697
            | (have j1 := b8e147 y x
               grind)
            | exact resolve b8e4697 b8e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147 b8e4697
          have b8e15702 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e15700
          have b8e15710 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e15702
               have r₂ := b8e21
               grind)
            | exact resolve b8e15702 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15702
          have b8e15723 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e15710
               grind)
            | exact superpose b8e15710 b8e23
            | exact resolve b8e23 b8e15710
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15710
          have b8e15789 : False := by grind
          exact b8e15789

/-- `Equation3475`: `x ◇ x = y ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation3475 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3475 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3475.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
        intro X0 X1
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x x) = (M.op y x) := by grind
      have b0e20 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
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
      have b0e24 : (M.op y y) = (M.op x (M.op (M.op x x) x)) := by
        first
        | (have i₁ := b0e11 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e27 : (M.op x x) = (M.op y y) := by
        first
        | (have i₁ := b0e24
           have i₂ := b0e11 x x
           grind)
        | exact superpose b0e11 b0e24
        | exact resolve b0e24 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24
      have b0e35 : ∀ X0 : G, (M.op x x) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b0e14 y X0
           have i₂ := b0e27
           grind)
        | exact superpose b0e27 b0e14
        | (have j0 := b0e14 y X0
           grind)
        | exact resolve b0e14 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) := by
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
      have b0e40 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
      have b0e41 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e40
      have b0e45 : (M.op y y) = (k x y) := by grind
      clear b0e37
      have b0e46 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e42
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e42
        | exact resolve b0e42 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e48 : (M.op x x) = (k x y) := by
        first
        | (have i₁ := b0e45
           have i₂ := b0e27
           grind)
        | exact superpose b0e27 b0e45
        | exact resolve b0e45 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e50 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
      have b0e53 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
      have b0e74 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (M.op X0 X0) X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X0
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e11 X0 X0
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 X1
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
      have b0e86 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e16 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e94 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e83 X0 X1
           have i₂ := b0e53 X1
           grind)
        | exact superpose b0e53 b0e83
        | (have j0 := b0e83 X0 X1
           grind)
        | exact resolve b0e83 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83
      have b0e97 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e74 X0 X1
           have i₂ := b0e11 X0 X0
           grind)
        | exact superpose b0e11 b0e74
        | (have j0 := b0e74 X0 X1
           grind)
        | exact resolve b0e74 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74
      have b0e100 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e94 X0 X1
           have i₂ := b0e53 X0
           grind)
        | exact superpose b0e53 b0e94
        | (have j0 := b0e94 X0 X1
           grind)
        | exact resolve b0e94 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e94
      have b0e101 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e97 X0 X1
           have j1 := b0e86 X1 X0
           grind)
        | (have r₁ := b0e97 X0 X1
           have r₂ := b0e86 X0 X1
           grind)
        | (have r₁ := b0e97 X1 X0
           have r₂ := b0e86 X0 X1
           grind)
        | (have r₁ := b0e97 X1 X1
           have r₂ := b0e86 X1 X1
           grind)
        | exact resolve b0e97 b0e86
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e86 b0e97
      have b0e120 : ∀ X0 : G, (σ (k x y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e14 (σ y) X0
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e14
        | (have j0 := b0e14 (σ y) X0
           grind)
        | exact resolve b0e14 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e126 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (σ (M.op x x)) ∨ (M.op X0 X0) = (k (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e120 X0
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e120
        | (have j0 := b0e120 X0
           grind)
        | exact resolve b0e120 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e120
      have b0e289 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e21 X1 X0
           have i₂ := b0e101 (τ X1) X0
           grind)
        | exact superpose b0e101 b0e21
        | (have j1 := b0e101 (τ X1) X0
           grind)
        | exact resolve b0e21 b0e101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21
      have b0e4004 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e100 x y
           grind)
        | exact superpose b0e100 b0e18
        | (have j1 := b0e100 x y
           grind)
        | exact resolve b0e18 b0e100
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e100
      have b0e4166 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e4004
           have i₂ := b0e27
           grind)
        | exact superpose b0e27 b0e4004
        | exact resolve b0e4004 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27 b0e4004
      have b0e4167 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
      clear b0e4166
      have b0e9017 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e289 X0 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e289
        | exact resolve b0e289 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e289
      have b0e9249 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e9017 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e9017
        | (have j0 := b0e9017 X0 X1
           grind)
        | exact resolve b0e9017 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9017
      have b0e13277 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e4167
           have i₂ := b0e101 y x
           grind)
        | exact superpose b0e101 b0e4167
        | (have j1 := b0e101 y x
           grind)
        | exact resolve b0e4167 b0e101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e101
      have b0e13278 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e13277
      have b0e26964 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e13278
           grind)
        | exact superpose b0e13278 b0e18
        | exact resolve b0e18 b0e13278
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e26971 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e126 (σ x)
           have i₂ := b0e13278
           grind)
        | exact superpose b0e13278 b0e126
        | (have j0 := b0e126 (σ x)
           grind)
        | (have r₁ := b0e126 (σ x)
           have r₂ := b0e13278
           grind)
        | exact resolve b0e126 b0e13278
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e126 b0e13278
      have b0e27027 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e26971
      have b0e27061 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e27027
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e27027
        | exact resolve b0e27027 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27027
      have b0e27084 : (σ (M.op x x)) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e27061
           have i₂ := b0e53 x
           grind)
        | exact superpose b0e53 b0e27061
        | exact resolve b0e27061 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53 b0e27061
      have b0e27674 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e9249 y x
           have i₂ := b0e27084
           grind)
        | exact superpose b0e27084 b0e9249
        | (have j0 := b0e9249 y x
           grind)
        | exact resolve b0e9249 b0e27084
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9249
      have b0e27675 : (τ (σ (M.op x x))) = (k y x) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e27084
           grind)
        | exact superpose b0e27084 b0e12
        | exact resolve b0e12 b0e27084
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27084
      have b0e27715 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e27674
      have b0e27750 : (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e27675
           have i₂ := b0e12 (M.op x x)
           grind)
        | exact superpose b0e12 b0e27675
        | exact resolve b0e27675 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27675
      have b0e27751 : (M.op x y) = (M.op x x) := by
        first
        | (have r₁ := b0e27715
           have r₂ := b0e26964
           grind)
        | exact resolve b0e27715 b0e26964
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26964 b0e27715
      have b0e27771 : (M.op x x) = (k y x) := by
        first
        | (have j1 := b0e35 x
           grind)
        | (have r₁ := b0e27750
           have r₂ := b0e35 x
           grind)
        | exact resolve b0e27750 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e27750
      have b0e28532 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e4167
           have i₂ := b0e27771
           grind)
        | exact superpose b0e27771 b0e4167
        | exact resolve b0e4167 b0e27771
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4167 b0e27771
      have b0e28562 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e28532
           have i₂ := b0e27751
           grind)
        | exact superpose b0e27751 b0e28532
        | exact resolve b0e28532 b0e27751
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28532
      have b0e28563 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
      clear b0e28562
      have b0e28826 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e28563
           grind)
        | exact superpose b0e28563 b0e18
        | exact resolve b0e18 b0e28563
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28563
      have b0e28934 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e28826
           have i₂ := b0e27751
           grind)
        | exact superpose b0e27751 b0e28826
        | exact resolve b0e28826 b0e27751
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27751 b0e28826
      have b0e28935 : False := by grind
      exact b0e28935
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : (M.op x x) = (M.op y x) := by grind
        have b1e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : (M.op y y) = (M.op x (M.op (M.op x x) x)) := by
          first
          | (have i₁ := b1e12 y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b1e26
             have i₂ := b1e12 x x
             grind)
          | exact superpose b1e12 b1e26
          | exact resolve b1e26 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e50 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
        clear b1e50
        have b1e56 : (M.op (σ y) (σ x)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e52
          | exact resolve b1e52 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e59 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e51 y
             grind)
          | exact superpose b1e51 b1e56
          | exact resolve b1e56 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e60 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e29
             grind)
          | exact superpose b1e29 b1e59
          | exact resolve b1e59 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29 b1e59
        have b1e62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e51 (σ X0)
             grind)
          | exact superpose b1e51 b1e18
          | exact resolve b1e18 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e62 X0
             have i₂ := b1e51 X0
             grind)
          | exact superpose b1e51 b1e62
          | exact resolve b1e62 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e62
        have b1e129 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e60
             grind)
          | exact superpose b1e60 b1e21
          | exact resolve b1e21 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e134 : False := by grind
        exact b1e134
      · have b2e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x x) = (M.op y x) := by grind
        have b2e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e26 : (M.op y y) = (M.op x (M.op (M.op x x) x)) := by
          first
          | (have i₁ := b2e12 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b2e26
             have i₂ := b2e12 x x
             grind)
          | exact superpose b2e12 b2e26
          | exact resolve b2e26 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e45 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) := by
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
        have b2e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e51 : (M.op y y) = (k x y) := by grind
        clear b2e45
        have b2e53 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b2e51
             have i₂ := b2e29
             grind)
          | exact superpose b2e29 b2e51
          | exact resolve b2e51 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51
        have b2e55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e48 (σ X0)
             grind)
          | exact superpose b2e48 b2e18
          | exact resolve b2e18 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e55 X0
             have i₂ := b2e48 X0
             grind)
          | exact superpose b2e48 b2e55
          | exact resolve b2e55 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48 b2e55
        have b2e92 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
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
        have b2e228 : (M.op (σ y) (σ x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e60 y
             grind)
          | exact superpose b2e60 b2e22
          | exact resolve b2e22 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e241 : (M.op (σ y) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e228
             have i₂ := b2e29
             grind)
          | exact superpose b2e29 b2e228
          | exact resolve b2e228 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29 b2e228
        have b2e2835 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e92 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e92
        have b2e2836 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e2835
             have r₂ := b2e21
             grind)
          | exact resolve b2e2835 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2835
        have b2e2841 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e2836
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e2836
          | exact resolve b2e2836 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2836
        have b2e2845 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e2841
             have i₂ := b2e53
             grind)
          | exact superpose b2e53 b2e2841
          | exact resolve b2e2841 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53 b2e2841
        have b2e2847 : False := by grind
        exact b2e2847
  · rcases eq_or_ne (M.op y x) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b3e21 : (M.op y x) = (M.op y y) := by grind
        have b3e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e41 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (σ x))) := by
          first
          | (have i₁ := b3e12 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e41
             have i₂ := b3e12 (σ x) (σ x)
             grind)
          | exact superpose b3e12 b3e41
          | exact resolve b3e41 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e55 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e57 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e55
        have b3e60 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e57
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e57
          | exact resolve b3e57 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57
        have b3e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e56 (σ X0)
             grind)
          | exact superpose b3e56 b3e18
          | exact resolve b3e18 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e63 X0
             have i₂ := b3e56 X0
             grind)
          | exact superpose b3e56 b3e63
          | exact resolve b3e63 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e82 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e15
          | exact resolve b3e15 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e84 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e82
        have b3e85 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e84
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e84
          | exact resolve b3e84 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e84
        have b3e86 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e85
             have i₂ := b3e56 y
             grind)
          | exact superpose b3e56 b3e85
          | exact resolve b3e85 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56 b3e85
        have b3e87 : (σ (k x y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e86
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e86
          | exact resolve b3e86 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e86
        have b3e153 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e60
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e60
          | exact resolve b3e60 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42 b3e60
        have b3e166 : (M.op (σ x) (σ x)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e153
             have i₂ := b3e87
             grind)
          | exact superpose b3e87 b3e153
          | exact resolve b3e153 b3e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e87 b3e153
        have b3e170 : (σ (M.op y x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e166
             have i₂ := b3e70 x
             grind)
          | exact superpose b3e70 b3e166
          | exact resolve b3e166 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70 b3e166
        have b3e177 : (M.op y x) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b3e13 (M.op y x)
             have i₂ := b3e170
             grind)
          | exact superpose b3e170 b3e13
          | exact resolve b3e13 b3e170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e170
        have b3e178 : (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b3e177
             have i₂ := b3e13 (M.op x x)
             grind)
          | exact superpose b3e13 b3e177
          | exact resolve b3e177 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e177
        have b3e182 : False := by grind
        exact b3e182
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op x x) ≠ (M.op y x) := by grind
          have b4e22 : (M.op y x) = (M.op y y) := by grind
          have b4e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b4e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
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
          have b4e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e32 : (M.op y x) = (M.op y (M.op (M.op y x) y)) := by
            first
            | (have i₁ := b4e13 y y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e68 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) ≠ (M.op X0 (M.op (M.op X1 X0) X0)) ∨ (M.op X0 (M.op (M.op X1 X0) X0)) = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X0 X0
               have i₂ := b4e13 X0 X1
               grind)
            | exact superpose b4e13 b4e16
            | exact resolve b4e16 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e69 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e71 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
          clear b4e69
          have b4e72 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (k X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e68 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e74 : (M.op (σ y) (σ x)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e71
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e71
            | exact resolve b4e71 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e76 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e74
               have i₂ := b4e70 y
               grind)
            | exact superpose b4e70 b4e74
            | exact resolve b4e74 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74
          have b4e77 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e76
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e76
            | exact resolve b4e76 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e76
          have b4e79 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e70 (σ X0)
               grind)
            | exact superpose b4e70 b4e19
            | exact resolve b4e19 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b4e26 X0 (τ X0)
               have i₂ := b4e70 (τ X0)
               grind)
            | exact superpose b4e70 b4e26
            | exact resolve b4e26 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e85 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e82 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e82
            | exact resolve b4e82 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e82
          have b4e88 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e79 X0
               have i₂ := b4e70 X0
               grind)
            | exact superpose b4e70 b4e79
            | exact resolve b4e79 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e79
          have b4e91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e85 X0
               have i₂ := b4e70 X0
               grind)
            | exact superpose b4e70 b4e85
            | exact resolve b4e85 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85
          have b4e102 : (M.op (σ x) (σ x)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e77
               grind)
            | exact superpose b4e77 b4e23
            | exact resolve b4e23 b4e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e107 : (σ (M.op y x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e102
               have i₂ := b4e88 x
               grind)
            | exact superpose b4e88 b4e102
            | exact resolve b4e102 b4e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102
          have b4e126 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (M.op X0 X0) X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e13 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X0 X1
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e127 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e17 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X1 X0
               have j1 := b4e18 X1 X0
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
          have b4e136 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
          have b4e141 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e142 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e144 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e127 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e127
          have b4e149 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e136 X0 X1
               have i₂ := b4e88 X1
               grind)
            | exact superpose b4e88 b4e136
            | (have j0 := b4e136 X0 X1
               grind)
            | exact resolve b4e136 b4e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e136
          have b4e152 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e144 X0 X1
               have j1 := b4e142 X0 X1
               grind)
            | (have r₁ := b4e144 X0 X1
               have r₂ := b4e142 X0 X1
               grind)
            | (have r₁ := b4e144 X1 X0
               have r₂ := b4e142 X0 X1
               grind)
            | (have r₁ := b4e144 X1 X1
               have r₂ := b4e142 X1 X1
               grind)
            | exact resolve b4e144 b4e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142 b4e144
          have b4e153 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e126 X0 X1
               have i₂ := b4e13 X0 X0
               grind)
            | exact superpose b4e13 b4e126
            | (have j0 := b4e126 X0 X1
               grind)
            | exact resolve b4e126 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e126
          have b4e159 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e149 X0 X1
               have i₂ := b4e88 X0
               grind)
            | exact superpose b4e88 b4e149
            | (have j0 := b4e149 X0 X1
               grind)
            | exact resolve b4e149 b4e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e149
          have b4e160 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e153 X0 X1
               have j1 := b4e141 X1 X0
               grind)
            | (have r₁ := b4e153 X0 X1
               have r₂ := b4e141 X0 X1
               grind)
            | (have r₁ := b4e153 X1 X0
               have r₂ := b4e141 X0 X1
               grind)
            | (have r₁ := b4e153 X1 X1
               have r₂ := b4e141 X1 X1
               grind)
            | exact resolve b4e153 b4e141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e141 b4e153
          have b4e177 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (σ X0) X1
               have i₂ := b4e88 X0
               grind)
            | exact superpose b4e88 b4e16
            | (have j0 := b4e16 (σ X0) X1
               grind)
            | exact resolve b4e16 b4e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e209 : ∀ X0 X1 : G, (σ (M.op X0 (M.op (M.op (τ X1) X0) X0))) = (k (σ (τ X1)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e26 X1 (τ X1)
               have i₂ := b4e72 X0 (τ X1)
               grind)
            | exact superpose b4e72 b4e26
            | exact resolve b4e26 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e72
          have b4e210 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 (M.op (M.op (τ X1) X0) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e209 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e209
            | exact resolve b4e209 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e209
          have b4e295 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e160 X0 X1
               grind)
            | (have i₁ := b4e17 X1 X1
               have i₂ := b4e160 X0 X1
               grind)
            | exact superpose b4e160 b4e17
            | (have j0 := b4e17 X0 X0
               have j1 := b4e160 X1 X0
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e160 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e160 X0 X0
               grind)
            | exact resolve b4e17 b4e160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e302 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X2)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X2
               have i₂ := b4e160 X1 X0
               grind)
            | (have i₁ := b4e13 X0 X1
               have i₂ := b4e160 X0 X0
               grind)
            | exact superpose b4e160 b4e13
            | (have j1 := b4e160 X1 X0
               grind)
            | exact resolve b4e13 b4e160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e309 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e160 (σ X1) (σ X0)
               grind)
            | exact superpose b4e160 b4e19
            | (have j1 := b4e160 (σ X1) (σ X0)
               grind)
            | exact resolve b4e19 b4e160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e316 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e295 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e295
          have b4e320 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e309 X0 X1
               have i₂ := b4e88 X0
               grind)
            | exact superpose b4e88 b4e309
            | (have j0 := b4e309 X0 X1
               grind)
            | exact resolve b4e309 b4e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e309
          have b4e448 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (M.op X0 (M.op (M.op (τ (σ X1)) X0) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X1
               have i₂ := b4e210 X0 (σ X1)
               grind)
            | exact superpose b4e210 b4e19
            | exact resolve b4e19 b4e210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e210
          have b4e473 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (M.op X0 (M.op (M.op X1 X0) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e448 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e448
            | exact resolve b4e448 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e448
          have b4e493 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (M.op X0 (M.op (M.op X1 X0) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e473 X0 X1
               have i₂ := b4e70 X1
               grind)
            | exact superpose b4e70 b4e473
            | exact resolve b4e473 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70 b4e473
          have b4e1815 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e152 (σ X1) (σ X0)
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e152
            | (have j0 := b4e152 (σ X1) (σ X0)
               grind)
            | exact resolve b4e152 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e152
          have b4e1912 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1815 X0 X1
               have i₂ := b4e88 X0
               grind)
            | exact superpose b4e88 b4e1815
            | (have j0 := b4e1815 X0 X1
               grind)
            | exact resolve b4e1815 b4e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1815
          have b4e1931 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1912 X0 X1
               have i₂ := b4e88 X0
               grind)
            | exact superpose b4e88 b4e1912
            | (have j0 := b4e1912 X0 X1
               grind)
            | exact resolve b4e1912 b4e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1912
          have b4e5189 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (σ X1) (σ X0)
               have i₂ := b4e159 X0 X1
               grind)
            | exact superpose b4e159 b4e16
            | (have j0 := b4e16 (σ X1) (σ X0)
               have j1 := b4e159 X0 X1
               grind)
            | exact resolve b4e16 b4e159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e5286 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e159 x y
               grind)
            | exact superpose b4e159 b4e20
            | (have j1 := b4e159 x y
               grind)
            | exact resolve b4e20 b4e159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e5326 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (σ X0) (σ X1)
               have i₂ := b4e159 X1 X0
               grind)
            | exact superpose b4e159 b4e16
            | (have j0 := b4e16 (σ X0) (σ X1)
               have j1 := b4e159 X1 X0
               grind)
            | exact resolve b4e16 b4e159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e5360 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e159 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e5363 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e159 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e159
          have b4e5456 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e5326 X0 X1
               have j1 := b4e177 X0 (σ X1)
               grind)
            | (have r₁ := b4e5326 X0 X0
               have r₂ := b4e177 X0 (σ X0)
               grind)
            | (have r₁ := b4e5326 X0 X1
               have r₂ := b4e177 X0 (σ X1)
               grind)
            | exact resolve b4e5326 b4e177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5326
          have b4e5465 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e5286
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e5286
            | exact resolve b4e5286 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5286
          have b4e5479 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e5189 X0 X1
               have j1 := b4e177 X1 (σ X0)
               grind)
            | (have r₁ := b4e5189 X0 X0
               have r₂ := b4e177 X0 (σ X0)
               grind)
            | exact resolve b4e5189 b4e177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e177 b4e5189
          have b4e5544 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e5456 X0 X1
               have i₂ := b4e88 X0
               grind)
            | exact superpose b4e88 b4e5456
            | (have j0 := b4e5456 X0 X1
               grind)
            | exact resolve b4e5456 b4e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5456
          have b4e5560 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e5479 X0 X1
               have i₂ := b4e88 X1
               grind)
            | exact superpose b4e88 b4e5479
            | (have j0 := b4e5479 X0 X1
               grind)
            | (have r₁ := b4e5479 X0 X0
               have r₂ := b4e88 X0
               grind)
            | exact resolve b4e5479 b4e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5479
          have b4e5599 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e5544 X0 X1
               have i₂ := b4e88 X1
               grind)
            | exact superpose b4e88 b4e5544
            | (have j0 := b4e5544 X0 X1
               grind)
            | exact resolve b4e5544 b4e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5544
          have b4e5609 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e5560 X0 X1
               have i₂ := b4e88 X0
               grind)
            | exact superpose b4e88 b4e5560
            | (have j0 := b4e5560 X0 X1
               grind)
            | exact resolve b4e5560 b4e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5560
          have b4e5634 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e5599 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e5599
            | (have j0 := b4e5599 X0 X1
               grind)
            | exact resolve b4e5599 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5599
          have b4e5639 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e5609 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e5609
            | (have j0 := b4e5609 X0 X1
               grind)
            | exact resolve b4e5609 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5609
          have b4e10781 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e493 x X0
               have i₂ := b4e302 X0 X1 x
               grind)
            | (have i₁ := b4e493 X0 X1
               have i₂ := b4e302 X0 (M.op (M.op X1 X0) X0) x
               grind)
            | exact superpose b4e302 b4e493
            | (have j1 := b4e302 X0 X1 x
               grind)
            | exact resolve b4e493 b4e302
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e302 b4e493
          have b4e17153 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e320 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e17154 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e320 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e320
          have b4e80157 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e5634 X1 X0
               have i₂ := b4e316 X0 X1
               grind)
            | exact superpose b4e316 b4e5634
            | (have j0 := b4e5634 X0 X1
               have j1 := b4e316 X0 X1
               grind)
            | exact resolve b4e5634 b4e316
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e80271 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (k (τ X0) X1)) ∨ (σ (k (τ X0) X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e5634 (τ X0) X1
               have i₂ := b4e91 X0
               grind)
            | exact superpose b4e91 b4e5634
            | (have j0 := b4e5634 (τ X0) X1
               grind)
            | exact resolve b4e5634 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5634
          have b4e80289 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e80157 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80157
          have b4e80304 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (k (τ X0) X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have j0 := b4e80271 X0 X1
               have j1 := b4e17154 X1 (τ X0)
               grind)
            | (have r₁ := b4e80271 X0 X0
               have r₂ := b4e17154 X0 (τ X0)
               grind)
            | exact resolve b4e80271 b4e17154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17154 b4e80271
          have b4e80394 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e80304 X0 X1
               have i₂ := b4e25 X0 X1
               grind)
            | exact superpose b4e25 b4e80304
            | (have j0 := b4e80304 X0 X1
               grind)
            | exact resolve b4e80304 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80304
          have b4e80428 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e80394 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e80394
            | (have j0 := b4e80394 X0 X1
               grind)
            | exact resolve b4e80394 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80394
          have b4e80595 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e80428 X1 X0
               have i₂ := b4e160 X1 (σ X0)
               grind)
            | exact superpose b4e160 b4e80428
            | (have j0 := b4e80428 X1 X0
               have j1 := b4e160 X1 (σ X0)
               grind)
            | (have r₁ := b4e80428 (σ X1) X1
               have r₂ := b4e160 (σ X1) (σ X1)
               grind)
            | exact resolve b4e80428 b4e160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e160 b4e80428
          have b4e80649 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e80595 X0 X1
               have i₂ := b4e88 X0
               grind)
            | exact superpose b4e88 b4e80595
            | (have j0 := b4e80595 X0 X1
               grind)
            | exact resolve b4e80595 b4e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80595
          have b4e80650 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b4e80649 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80649
          have b4e81078 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op X1 X1)) ∨ (σ (k (τ X0) X1)) = (σ (M.op X1 X1)) ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e5639 X1 (τ X0)
               have i₂ := b4e91 X0
               grind)
            | exact superpose b4e91 b4e5639
            | (have j0 := b4e5639 X1 (τ X0)
               grind)
            | exact resolve b4e5639 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5639
          have b4e81108 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op X1 X1)) ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have j0 := b4e81078 X0 X1
               have j1 := b4e17153 X1 (τ X0)
               grind)
            | (have r₁ := b4e81078 X0 X0
               have r₂ := b4e17153 X0 (τ X0)
               grind)
            | exact resolve b4e81078 b4e17153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17153 b4e81078
          have b4e81177 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) ≠ (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e81108 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e81108
            | (have j0 := b4e81108 X0 X1
               grind)
            | exact resolve b4e81108 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81108
          have b4e81198 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e81177 X0 X1
               have i₂ := b4e25 X0 X1
               grind)
            | exact superpose b4e25 b4e81177
            | (have j0 := b4e81177 X0 X1
               grind)
            | exact resolve b4e81177 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e81177
          have b4e84439 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e81198 X1 (τ X0)
               have i₂ := b4e91 X0
               grind)
            | exact superpose b4e91 b4e81198
            | (have j0 := b4e81198 X1 (τ X0)
               grind)
            | (have r₁ := b4e81198 X0 (τ X0)
               have r₂ := b4e91 X0
               grind)
            | exact resolve b4e81198 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91 b4e81198
          have b4e84456 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e84439 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e84439
            | (have j0 := b4e84439 X0 X1
               grind)
            | exact resolve b4e84439 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84439
          have b4e89332 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e80650 X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e80650
            | (have j0 := b4e80650 X0 (σ y)
               grind)
            | exact resolve b4e80650 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e89335 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e80650 X1 (σ X0)
               have i₂ := b4e88 X0
               grind)
            | exact superpose b4e88 b4e80650
            | (have j0 := b4e80650 X1 (σ X0)
               grind)
            | exact resolve b4e80650 b4e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e88 b4e80650
          have b4e89606 : ∀ X0 : G, (σ (M.op y x)) ≠ (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e89332 X0
               have i₂ := b4e77
               grind)
            | exact superpose b4e77 b4e89332
            | (have j0 := b4e89332 X0
               grind)
            | exact resolve b4e89332 b4e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77 b4e89332
          have b4e93028 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e5363 X1 X0
               have i₂ := b4e316 X1 X0
               grind)
            | exact superpose b4e316 b4e5363
            | (have j0 := b4e5363 X1 X0
               have j1 := b4e316 X0 X1
               grind)
            | exact resolve b4e5363 b4e316
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e316 b4e5363
          have b4e93251 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e93028 X0 X1
               have j1 := b4e80289 X0 X1
               grind)
            | (have r₁ := b4e93028 X0 X1
               have r₂ := b4e80289 X0 X1
               grind)
            | (have r₁ := b4e93028 X1 X0
               have r₂ := b4e80289 X0 X1
               grind)
            | exact resolve b4e93028 b4e80289
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80289 b4e93028
          have b4e93306 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e93251 X0 X1
               have j1 := b4e89335 X0 X1
               grind)
            | (have r₁ := b4e93251 X0 X0
               have r₂ := b4e89335 X0 X0
               grind)
            | (have r₁ := b4e93251 X0 X1
               have r₂ := b4e89335 X0 X1
               grind)
            | exact resolve b4e93251 b4e89335
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89335 b4e93251
          have b4e93329 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e93306 X0 X1
               have j1 := b4e84456 X1 X0
               grind)
            | (have r₁ := b4e93306 X0 X1
               have r₂ := b4e84456 X0 X1
               grind)
            | (have r₁ := b4e93306 X1 X0
               have r₂ := b4e84456 X0 X1
               grind)
            | exact resolve b4e93306 b4e84456
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84456 b4e93306
          have b4e94570 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e93329 y x
               grind)
            | exact superpose b4e93329 b4e20
            | (have j1 := b4e93329 y x
               grind)
            | exact resolve b4e20 b4e93329
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93329
          have b4e95104 : (M.op x y) = (k y x) := by
            first
            | (have j1 := b4e10781 x y
               grind)
            | (have r₁ := b4e94570
               have r₂ := b4e10781 x y
               grind)
            | exact resolve b4e94570 b4e10781
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10781 b4e94570
          have b4e96059 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e5465
               have i₂ := b4e95104
               grind)
            | exact superpose b4e95104 b4e5465
            | exact resolve b4e5465 b4e95104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5465
          have b4e96062 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e5360 x y
               have i₂ := b4e95104
               grind)
            | exact superpose b4e95104 b4e5360
            | (have j0 := b4e5360 x y
               grind)
            | exact resolve b4e5360 b4e95104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5360
          have b4e96068 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
          clear b4e96059
          have b4e96074 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b4e96062
               have r₂ := b4e20
               grind)
            | exact resolve b4e96062 b4e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96062
          have b4e96075 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have j1 := b4e89606 x
               grind)
            | (have r₁ := b4e96068
               have r₂ := b4e89606 x
               grind)
            | exact resolve b4e96068 b4e89606
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89606 b4e96068
          have b4e96077 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e96074
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e96074
            | exact resolve b4e96074 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96074
          have b4e96078 : (σ (M.op y x)) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e96077
               have i₂ := b4e96075
               grind)
            | exact superpose b4e96075 b4e96077
            | exact resolve b4e96077 b4e96075
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96077
          have b4e96079 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have r₁ := b4e96078
               have r₂ := b4e107
               grind)
            | exact resolve b4e96078 b4e107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96078
          have b4e97726 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op y y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e1931 y x
               have i₂ := b4e96075
               grind)
            | exact superpose b4e96075 b4e1931
            | (have j0 := b4e1931 y x
               grind)
            | exact resolve b4e1931 b4e96075
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1931 b4e96075
          have b4e97912 : (σ (M.op y x)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op y y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e97726
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e97726
            | exact resolve b4e97726 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e97726
          have b4e97955 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op y y)) = (σ (k y x)) := by
            first
            | (have r₁ := b4e97912
               have r₂ := b4e107
               grind)
            | exact resolve b4e97912 b4e107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e107 b4e97912
          have b4e97977 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e97955
               have i₂ := b4e95104
               grind)
            | exact superpose b4e95104 b4e97955
            | exact resolve b4e97955 b4e95104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e97955
          have b4e97991 : (σ (M.op y y)) = (σ (k y x)) := by
            first
            | (have r₁ := b4e97977
               have r₂ := b4e96079
               grind)
            | exact resolve b4e97977 b4e96079
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96079 b4e97977
          have b4e98001 : (σ (M.op x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e97991
               have i₂ := b4e95104
               grind)
            | exact superpose b4e95104 b4e97991
            | exact resolve b4e97991 b4e95104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e95104 b4e97991
          have b4e98008 : (σ (M.op x y)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e98001
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e98001
            | exact resolve b4e98001 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e98001
          have b4e99930 : (M.op y x) = (τ (σ (M.op x y))) := by
            first
            | (have i₁ := b4e14 (M.op y x)
               have i₂ := b4e98008
               grind)
            | exact superpose b4e98008 b4e14
            | exact resolve b4e14 b4e98008
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e98008
          have b4e100040 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b4e99930
               have i₂ := b4e14 (M.op x y)
               grind)
            | exact superpose b4e14 b4e99930
            | exact resolve b4e99930 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99930
          have b4e100686 : (M.op x y) ≠ (M.op x x) := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e100040
               grind)
            | exact superpose b4e100040 b4e21
            | exact resolve b4e21 b4e100040
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e100687 : (M.op x y) = (M.op y (M.op (M.op x y) y)) := by
            first
            | (have i₁ := b4e32
               have i₂ := b4e100040
               grind)
            | exact superpose b4e100040 b4e32
            | exact resolve b4e32 b4e100040
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32 b4e100040
          have b4e100884 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e100687
               have i₂ := b4e13 x y
               grind)
            | exact superpose b4e13 b4e100687
            | exact resolve b4e100687 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e100687
          have b4e100941 : False := by grind
          exact b4e100941
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x x) ≠ (M.op y x) := by grind
          have b5e22 : (M.op y x) = (M.op y y) := by grind
          have b5e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e67 (σ X0)
               grind)
            | exact superpose b5e67 b5e19
            | exact resolve b5e19 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e72 X0
               have i₂ := b5e67 X0
               grind)
            | exact superpose b5e67 b5e72
            | exact resolve b5e72 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67 b5e72
          have b5e90 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 X0) = (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e132 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
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
          have b5e955 : (M.op x x) = (M.op y x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e90 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90
          have b5e957 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e955
               have r₂ := b5e21
               grind)
            | exact resolve b5e955 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e955
          have b5e3704 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e132 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e132
          have b5e3705 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e3704
               have r₂ := b5e23
               grind)
            | exact resolve b5e3704 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3704
          have b5e3710 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e3705
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e3705
            | exact resolve b5e3705 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3705
          have b5e3714 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e3710
               have i₂ := b5e957
               grind)
            | exact superpose b5e957 b5e3710
            | exact resolve b5e3710 b5e957
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e957 b5e3710
          have b5e3719 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e3714
               grind)
            | exact superpose b5e3714 b5e23
            | exact resolve b5e23 b5e3714
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3714
          have b5e3761 : False := by grind
          exact b5e3761
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b6e21 : (M.op y x) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e52 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e54 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e52
        have b6e56 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e54
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e54
          | exact resolve b6e54 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e76 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e56
             grind)
          | exact superpose b6e56 b6e15
          | exact resolve b6e15 b6e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e78 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e76
        have b6e79 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e78
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e78
          | exact resolve b6e78 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78
        have b6e80 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e79
             have i₂ := b6e53 y
             grind)
          | exact superpose b6e53 b6e79
          | exact resolve b6e79 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53 b6e79
        have b6e135 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e80
             grind)
          | exact superpose b6e80 b6e13
          | exact resolve b6e13 b6e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80
        have b6e136 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e135
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e135
          | exact resolve b6e135 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e135
        have b6e169 : (M.op y x) = (M.op y y) ∨ (M.op x x) = (M.op y x) ∨ (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e136
             grind)
          | exact superpose b6e136 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e136
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e136
        have b6e170 : (M.op y x) = (M.op y y) ∨ (M.op x x) = (M.op y x) := by grind
        clear b6e169
        have b6e172 : (M.op x x) = (M.op y x) := by
          first
          | (have r₁ := b6e170
             have r₂ := b6e21
             grind)
          | exact resolve b6e170 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e170
        have b6e174 : False := by grind
        exact b6e174
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x x) ≠ (M.op y x) := by grind
          have b7e22 : (M.op y x) ≠ (M.op y y) := by grind
          have b7e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e66 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e68 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
          clear b7e66
          have b7e70 : (M.op (σ y) (σ x)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e68
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e68
            | exact resolve b7e68 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e71 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e67 y
               grind)
            | exact superpose b7e67 b7e70
            | exact resolve b7e70 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e67 (σ X0)
               grind)
            | exact superpose b7e67 b7e19
            | exact resolve b7e19 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e73 X0
               have i₂ := b7e67 X0
               grind)
            | exact superpose b7e67 b7e73
            | exact resolve b7e73 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67 b7e73
          have b7e92 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e94 : ∀ X0 : G, (M.op (σ y) X0) ≠ (σ (M.op y y)) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e92 X0
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e92
            | (have j0 := b7e92 X0
               grind)
            | exact resolve b7e92 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e95 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e23
            | exact resolve b7e23 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e100 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e95
               have i₂ := b7e82 x
               grind)
            | exact superpose b7e82 b7e95
            | exact resolve b7e95 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95
          have b7e119 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (M.op X0 X0) X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X0
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e13 X0 X0
               have i₂ := b7e18 X0 X1
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X0 X1
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e134 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e146 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e119 X0 X1
               have i₂ := b7e13 X0 X0
               grind)
            | exact superpose b7e13 b7e119
            | (have j0 := b7e119 X0 X1
               grind)
            | exact resolve b7e119 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e119
          have b7e153 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e146 X0 X1
               have j1 := b7e134 X1 X0
               grind)
            | (have r₁ := b7e146 X0 X1
               have r₂ := b7e134 X0 X1
               grind)
            | (have r₁ := b7e146 X1 X0
               have r₂ := b7e134 X0 X1
               grind)
            | (have r₁ := b7e146 X1 X1
               have r₂ := b7e134 X1 X1
               grind)
            | exact resolve b7e146 b7e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e134 b7e146
          have b7e1902 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e94 (σ x)
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e94
            | (have j0 := b7e94 (σ x)
               grind)
            | (have r₁ := b7e94 (σ x)
               have r₂ := b7e71
               grind)
            | exact resolve b7e94 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71 b7e94
          have b7e1913 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e1902
          have b7e1916 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e1913
               have i₂ := b7e82 x
               grind)
            | exact superpose b7e82 b7e1913
            | exact resolve b7e1913 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1913
          have b7e1919 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e1916
               have r₂ := b7e100
               grind)
            | exact resolve b7e1916 b7e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e100 b7e1916
          have b7e1921 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e1919
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e1919
            | exact resolve b7e1919 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1919
          have b7e1922 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e1921
               have i₂ := b7e82 x
               grind)
            | exact superpose b7e82 b7e1921
            | exact resolve b7e1921 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82 b7e1921
          have b7e1927 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e1922
               grind)
            | exact superpose b7e1922 b7e14
            | exact resolve b7e14 b7e1922
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1922
          have b7e1944 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e1927
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e1927
            | exact resolve b7e1927 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1927
          have b7e2232 : (M.op x x) = (M.op y x) ∨ (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b7e153 x y
               have i₂ := b7e1944
               grind)
            | exact superpose b7e1944 b7e153
            | (have j0 := b7e153 x y
               grind)
            | exact resolve b7e153 b7e1944
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e153 b7e1944
          have b7e2236 : (M.op y x) = (M.op y y) := by
            first
            | (have r₁ := b7e2232
               have r₂ := b7e21
               grind)
            | exact resolve b7e2232 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2232
          have b7e2242 : False := by grind
          exact b7e2242
        · have b8e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e42 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          clear b8e30
          have b8e63 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) ≠ (M.op X0 (M.op (M.op X1 X0) X0)) ∨ (M.op X0 (M.op (M.op X1 X0) X0)) = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X0
               have i₂ := b8e13 X0 X1
               grind)
            | exact superpose b8e13 b8e16
            | exact resolve b8e16 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e65 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (k X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e63 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
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
          have b8e70 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 (τ X0)
               have i₂ := b8e64 (τ X0)
               grind)
            | exact superpose b8e64 b8e26
            | exact resolve b8e26 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e73 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e70 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e70
            | exact resolve b8e70 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70
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
          clear b8e67
          have b8e79 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e73 X0
               have i₂ := b8e64 X0
               grind)
            | exact superpose b8e64 b8e73
            | exact resolve b8e73 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e85 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (M.op X2 X2) ∨ (M.op X2 X2) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e17 X2 X1
               have i₂ := b8e13 X1 X0
               grind)
            | exact superpose b8e13 b8e17
            | (have j0 := b8e17 X2 X1
               grind)
            | (have r₁ := b8e17 (M.op (M.op X0 X0) X0) X0
               have r₂ := b8e13 X0 X0
               grind)
            | exact resolve b8e17 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e93 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X0) X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e16
            | (have j0 := b8e16 (σ X0) X1
               grind)
            | exact resolve b8e16 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e116 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (M.op X0 X0) X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 X0
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e13 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X0 X1
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e127 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
          have b8e132 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e140 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e127 X0 X1
               have i₂ := b8e76 X1
               grind)
            | exact superpose b8e76 b8e127
            | (have j0 := b8e127 X0 X1
               grind)
            | exact resolve b8e127 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e127
          have b8e143 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e116 X0 X1
               have i₂ := b8e13 X0 X0
               grind)
            | exact superpose b8e13 b8e116
            | (have j0 := b8e116 X0 X1
               grind)
            | exact resolve b8e116 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e116
          have b8e146 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e140 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e140
            | (have j0 := b8e140 X0 X1
               grind)
            | exact resolve b8e140 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e140
          have b8e147 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e143 X0 X1
               have j1 := b8e132 X1 X0
               grind)
            | (have r₁ := b8e143 X0 X1
               have r₂ := b8e132 X0 X1
               grind)
            | (have r₁ := b8e143 X1 X0
               have r₂ := b8e132 X0 X1
               grind)
            | (have r₁ := b8e143 X1 X1
               have r₂ := b8e132 X1 X1
               grind)
            | exact resolve b8e143 b8e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e132 b8e143
          have b8e154 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (M.op (M.op (τ X1) X0) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e79 X1
               have i₂ := b8e13 (τ X1) X0
               grind)
            | exact superpose b8e13 b8e79
            | exact resolve b8e79 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e160 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e79 X0
               grind)
            | exact superpose b8e79 b8e14
            | exact resolve b8e14 b8e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e215 : ∀ X0 X1 : G, (τ (k X0 X0)) = (M.op X1 (M.op (M.op (τ X0) X1) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e65 X1 (τ X0)
               have i₂ := b8e42 X0 X0
               grind)
            | exact superpose b8e42 b8e65
            | exact resolve b8e65 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42 b8e65
          have b8e220 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (M.op (M.op (τ X0) X1) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e215 X0 X1
               have i₂ := b8e64 X0
               grind)
            | exact superpose b8e64 b8e215
            | exact resolve b8e215 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64 b8e215
          have b8e238 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X0 X1
               have i₂ := b8e147 X0 X1
               grind)
            | (have i₁ := b8e17 X1 X1
               have i₂ := b8e147 X0 X1
               grind)
            | exact superpose b8e147 b8e17
            | (have j0 := b8e17 X0 X0
               have j1 := b8e147 X1 X0
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e147 X0 X1
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e147 X0 X0
               grind)
            | exact resolve b8e17 b8e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e251 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e147 (σ X1) (σ X0)
               grind)
            | exact superpose b8e147 b8e19
            | (have j1 := b8e147 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e253 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X1 X0
               have i₂ := b8e147 (τ X1) X0
               grind)
            | exact superpose b8e147 b8e25
            | (have j1 := b8e147 (τ X1) X0
               grind)
            | exact resolve b8e25 b8e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e258 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e238 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e238
          have b8e262 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e251 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e251
            | (have j0 := b8e251 X0 X1
               grind)
            | exact resolve b8e251 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e251
          have b8e678 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 (M.op (M.op (τ (τ X1)) X0) X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b8e79 X1
               have i₂ := b8e154 X0 (τ X1)
               grind)
            | exact superpose b8e154 b8e79
            | exact resolve b8e79 b8e154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e154
          have b8e1018 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (τ (τ X0)) X1) X1)) = (τ (τ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e220 (τ X0) X1
               have i₂ := b8e160 X0
               grind)
            | exact superpose b8e160 b8e220
            | exact resolve b8e220 b8e160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e220
          have b8e3802 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X1) (σ X0)
               have i₂ := b8e146 X0 X1
               grind)
            | exact superpose b8e146 b8e16
            | (have j0 := b8e16 (σ X1) (σ X0)
               have j1 := b8e146 X0 X1
               grind)
            | exact resolve b8e16 b8e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3890 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e146 x y
               grind)
            | exact superpose b8e146 b8e20
            | (have j1 := b8e146 x y
               grind)
            | exact resolve b8e20 b8e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3928 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X0) (σ X1)
               have i₂ := b8e146 X1 X0
               grind)
            | exact superpose b8e146 b8e16
            | (have j0 := b8e16 (σ X0) (σ X1)
               have j1 := b8e146 X1 X0
               grind)
            | exact resolve b8e16 b8e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3965 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e146 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e146
          have b8e4045 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e3928 X0 X1
               have j1 := b8e93 X0 (σ X1)
               grind)
            | (have r₁ := b8e3928 X0 X0
               have r₂ := b8e93 X0 (σ X0)
               grind)
            | (have r₁ := b8e3928 X0 X1
               have r₂ := b8e93 X0 (σ X1)
               grind)
            | exact resolve b8e3928 b8e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3928
          have b8e4061 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e3802 X0 X1
               have j1 := b8e93 X1 (σ X0)
               grind)
            | (have r₁ := b8e3802 X0 X0
               have r₂ := b8e93 X0 (σ X0)
               grind)
            | exact resolve b8e3802 b8e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93 b8e3802
          have b8e4117 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e4045 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e4045
            | (have j0 := b8e4045 X0 X1
               grind)
            | exact resolve b8e4045 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4045
          have b8e4128 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e4061 X0 X1
               have i₂ := b8e76 X1
               grind)
            | exact superpose b8e76 b8e4061
            | (have j0 := b8e4061 X0 X1
               grind)
            | (have r₁ := b8e4061 X0 X0
               have r₂ := b8e76 X0
               grind)
            | exact resolve b8e4061 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4061
          have b8e4164 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e4117 X0 X1
               have i₂ := b8e76 X1
               grind)
            | exact superpose b8e76 b8e4117
            | (have j0 := b8e4117 X0 X1
               grind)
            | exact resolve b8e4117 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4117
          have b8e4170 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e4128 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e4128
            | (have j0 := b8e4128 X0 X1
               grind)
            | exact resolve b8e4128 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4128
          have b8e4193 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e4164 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e4164
            | (have j0 := b8e4164 X0 X1
               grind)
            | exact resolve b8e4164 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4164
          have b8e4196 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e4170 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e4170
            | (have j0 := b8e4170 X0 X1
               grind)
            | exact resolve b8e4170 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4170
          have b8e8578 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e253 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e253
            | exact resolve b8e253 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e253
          have b8e8811 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e8578 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e8578
            | (have j0 := b8e8578 X0 X1
               grind)
            | exact resolve b8e8578 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8578
          have b8e10132 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (M.op X0 (M.op (M.op (τ (τ (τ X1))) X0) X0))))) := by
            intro X0 X1
            first
            | (have i₁ := b8e79 X1
               have i₂ := b8e678 X0 (τ X1)
               grind)
            | exact superpose b8e678 b8e79
            | exact resolve b8e79 b8e678
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e678
          have b8e12945 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e262 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e12946 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e262 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e262
          have b8e14652 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (τ (τ (τ X0))) X1) X1)) = (τ (τ (τ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1018 (τ X0) X1
               have i₂ := b8e160 X0
               grind)
            | exact superpose b8e160 b8e1018
            | exact resolve b8e1018 b8e160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160 b8e1018
          have b8e57418 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (k (τ X0) X1)) ∨ (σ (k (τ X0) X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e4193 (τ X0) X1
               have i₂ := b8e79 X0
               grind)
            | exact superpose b8e79 b8e4193
            | (have j0 := b8e4193 (τ X0) X1
               grind)
            | exact resolve b8e4193 b8e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4193
          have b8e57444 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (k (τ X0) X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have j0 := b8e57418 X0 X1
               have j1 := b8e12946 X1 (τ X0)
               grind)
            | (have r₁ := b8e57418 X0 X0
               have r₂ := b8e12946 X0 (τ X0)
               grind)
            | exact resolve b8e57418 b8e12946
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e12946 b8e57418
          have b8e57512 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e57444 X0 X1
               have i₂ := b8e25 X0 X1
               grind)
            | exact superpose b8e25 b8e57444
            | (have j0 := b8e57444 X0 X1
               grind)
            | exact resolve b8e57444 b8e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57444
          have b8e57531 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e57512 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e57512
            | (have j0 := b8e57512 X0 X1
               grind)
            | exact resolve b8e57512 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57512
          have b8e57639 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X1 X0) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e57531 X0 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e57531
            | exact resolve b8e57531 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e57668 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e57531 X1 X0
               have i₂ := b8e147 X1 (σ X0)
               grind)
            | exact superpose b8e147 b8e57531
            | (have j0 := b8e57531 X1 X0
               have j1 := b8e147 X1 (σ X0)
               grind)
            | (have r₁ := b8e57531 (σ X1) X1
               have r₂ := b8e147 (σ X1) (σ X1)
               grind)
            | exact resolve b8e57531 b8e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147 b8e57531
          have b8e57703 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e57668 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e57668
            | (have j0 := b8e57668 X0 X1
               grind)
            | exact resolve b8e57668 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57668
          have b8e57704 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b8e57703 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57703
          have b8e57711 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e57639 X0 X1
               have i₂ := b8e79 X0
               grind)
            | exact superpose b8e79 b8e57639
            | (have j0 := b8e57639 X0 X1
               grind)
            | exact resolve b8e57639 b8e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57639
          have b8e57857 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op X1 X1)) ∨ (σ (k (τ X0) X1)) = (σ (M.op X1 X1)) ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e4196 X1 (τ X0)
               have i₂ := b8e79 X0
               grind)
            | exact superpose b8e79 b8e4196
            | (have j0 := b8e4196 X1 (τ X0)
               grind)
            | exact resolve b8e4196 b8e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4196
          have b8e57883 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op X1 X1)) ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have j0 := b8e57857 X0 X1
               have j1 := b8e12945 X1 (τ X0)
               grind)
            | (have r₁ := b8e57857 X0 X0
               have r₂ := b8e12945 X0 (τ X0)
               grind)
            | exact resolve b8e57857 b8e12945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e12945 b8e57857
          have b8e57944 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) ≠ (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e57883 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e57883
            | (have j0 := b8e57883 X0 X1
               grind)
            | exact resolve b8e57883 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57883
          have b8e57961 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e57944 X0 X1
               have i₂ := b8e25 X0 X1
               grind)
            | exact superpose b8e25 b8e57944
            | (have j0 := b8e57944 X0 X1
               grind)
            | exact resolve b8e57944 b8e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25 b8e57944
          have b8e60711 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e57961 X1 (τ X0)
               have i₂ := b8e79 X0
               grind)
            | exact superpose b8e79 b8e57961
            | (have j0 := b8e57961 X1 (τ X0)
               grind)
            | (have r₁ := b8e57961 X0 (τ X0)
               have r₂ := b8e79 X0
               grind)
            | exact resolve b8e57961 b8e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79 b8e57961
          have b8e60725 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e60711 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e60711
            | (have j0 := b8e60711 X0 X1
               grind)
            | exact resolve b8e60711 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60711
          have b8e62198 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e57704 X1 (σ X0)
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e57704
            | (have j0 := b8e57704 X1 (σ X0)
               grind)
            | exact resolve b8e57704 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57704
          have b8e63742 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (σ (σ (M.op X0 (M.op (M.op (τ (τ (τ X1))) X0) X0))))) ∨ (M.op X2 X2) = (k X2 X1) ∨ (M.op X1 X2) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e258 X1 X2
               have i₂ := b8e10132 X0 X1
               grind)
            | exact superpose b8e10132 b8e258
            | (have j0 := b8e258 X1 X2
               grind)
            | exact resolve b8e258 b8e10132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e258
          have b8e63813 : ∀ X0 X1 X2 : G, (M.op X2 X2) ≠ (σ (σ (σ (M.op X0 (M.op (M.op (τ (τ (τ X1))) X0) X0))))) ∨ (M.op X1 X2) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e60725 X1 X2
               have i₂ := b8e10132 X0 X1
               grind)
            | exact superpose b8e10132 b8e60725
            | (have j0 := b8e60725 X1 X2
               grind)
            | exact resolve b8e60725 b8e10132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10132 b8e60725
          have b8e64115 : ∀ X1 X2 : G, (M.op X2 X2) = (k X2 X1) ∨ (M.op X1 X2) = (k X2 X1) := by
            intro X1 X2
            first
            | (have j0 := b8e63742 x X1 X2
               have j1 := b8e63813 x X1 X2
               grind)
            | (have r₁ := b8e63742 x X1 X2
               have r₂ := b8e63813 x X1 X2
               grind)
            | exact resolve b8e63742 b8e63813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63742 b8e63813
          have b8e66522 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e64115 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64115
          have b8e69797 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e3890
               have i₂ := b8e8811 y x
               grind)
            | exact superpose b8e8811 b8e3890
            | (have j1 := b8e8811 y x
               grind)
            | (have r₁ := b8e3890
               have r₂ := b8e8811 y x
               grind)
            | exact resolve b8e3890 b8e8811
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3890 b8e8811
          have b8e69798 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e69797
          have b8e69814 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have j1 := b8e62198 y x
               grind)
            | (have r₁ := b8e69798
               have r₂ := b8e62198 y x
               grind)
            | exact resolve b8e69798 b8e62198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69798
          have b8e98862 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op (τ (τ (τ X0))) X1) X1) (M.op (τ (τ (τ (M.op X0 X0)))) (M.op (M.op (τ (τ (τ X0))) X1) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (M.op (M.op (τ (τ (τ X0))) X1) X1)
               have i₂ := b8e14652 X0 X1
               grind)
            | exact superpose b8e14652 b8e13
            | exact resolve b8e13 b8e14652
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e98871 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op (M.op (M.op (τ (τ (τ X0))) X1) X1) (M.op (τ (τ (τ (M.op X0 X0)))) (M.op (M.op (τ (τ (τ X0))) X1) X1))) ∨ (M.op X1 X2) = (M.op X2 X2) ∨ (M.op X2 X2) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e85 (M.op (M.op (τ (τ (τ X0))) X1) X1) X1 X2
               have i₂ := b8e14652 X0 X1
               grind)
            | exact superpose b8e14652 b8e85
            | (have j0 := b8e85 X0 X1 X2
               grind)
            | exact resolve b8e85 b8e14652
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85 b8e14652
          have b8e99232 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op (M.op (M.op (τ (τ (τ X0))) X1) X1) (M.op (τ (τ (τ (M.op X0 X0)))) (M.op (M.op (τ (τ (τ X0))) X1) X1))) ∨ (M.op X2 X2) = (k X2 X1) := by
            intro X0 X1 X2
            first
            | (have j0 := b8e98871 X0 X1 X2
               have j1 := b8e66522 X2 X1
               grind)
            | (have r₁ := b8e98871 X0 X1 X1
               have r₂ := b8e66522 X1 X1
               grind)
            | (have r₁ := b8e98871 X0 X1 X0
               have r₂ := b8e66522 X0 X1
               grind)
            | exact resolve b8e98871 b8e66522
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66522 b8e98871
          have b8e99494 : ∀ X1 X2 : G, (M.op X1 X1) ≠ (M.op X1 X2) ∨ (M.op X2 X2) = (k X2 X1) := by
            intro X1 X2
            first
            | (have i₁ := b8e99232 x X1 X2
               have i₂ := b8e98862 x X1
               grind)
            | exact superpose b8e98862 b8e99232
            | (have j0 := b8e99232 x X1 X2
               grind)
            | (have r₁ := b8e99232 x X1 X1
               have r₂ := b8e98862 x X1
               grind)
            | exact resolve b8e99232 b8e98862
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98862 b8e99232
          have b8e101174 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e99494 (σ x) (σ y)
               have i₂ := b8e69814
               grind)
            | exact superpose b8e69814 b8e99494
            | (have j0 := b8e99494 (σ x) (σ y)
               grind)
            | (have r₁ := b8e99494 x y
               have r₂ := b8e69814
               grind)
            | exact resolve b8e99494 b8e69814
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69814
          have b8e101269 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b8e101174
               have r₂ := b8e76 x
               grind)
            | exact resolve b8e101174 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e101174
          have b8e101327 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e101269
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e101269
            | exact resolve b8e101269 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e101269
          have b8e101345 : (σ (M.op y y)) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e101327
               have i₂ := b8e76 y
               grind)
            | exact superpose b8e76 b8e101327
            | exact resolve b8e101327 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76 b8e101327
          have b8e102027 : (τ (σ (M.op y y))) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e101345
               grind)
            | exact superpose b8e101345 b8e14
            | exact resolve b8e14 b8e101345
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e101345
          have b8e102143 : (M.op y y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e102027
               have i₂ := b8e14 (M.op y y)
               grind)
            | exact superpose b8e14 b8e102027
            | exact resolve b8e102027 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102027
          have b8e102165 : (M.op y y) = (k y x) := by
            first
            | (have j1 := b8e99494 x y
               grind)
            | (have r₁ := b8e102143
               have r₂ := b8e99494 x y
               grind)
            | exact resolve b8e102143 b8e99494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99494 b8e102143
          have b8e103762 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e3965 x y
               have i₂ := b8e102165
               grind)
            | exact superpose b8e102165 b8e3965
            | (have j0 := b8e3965 x y
               grind)
            | exact resolve b8e3965 b8e102165
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3965
          have b8e103765 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e57711 x y
               have i₂ := b8e102165
               grind)
            | exact superpose b8e102165 b8e57711
            | (have j0 := b8e57711 x y
               grind)
            | (have r₁ := b8e57711 x y
               have r₂ := b8e102165
               grind)
            | exact resolve b8e57711 b8e102165
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57711 b8e102165
          have b8e103768 : (M.op x y) = (M.op x x) := by grind
          clear b8e103765
          have b8e103770 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
          clear b8e103762
          have b8e103789 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have j1 := b8e62198 y x
               grind)
            | (have r₁ := b8e103770
               have r₂ := b8e62198 y x
               grind)
            | exact resolve b8e103770 b8e62198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62198 b8e103770
          have b8e104772 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e103789
               grind)
            | exact superpose b8e103789 b8e20
            | exact resolve b8e20 b8e103789
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e103789
          have b8e104985 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e104772
               have i₂ := b8e103768
               grind)
            | exact superpose b8e103768 b8e104772
            | exact resolve b8e104772 b8e103768
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e103768 b8e104772
          have b8e104986 : False := by grind
          exact b8e104986

/-- `Equation3475`: `x ◇ x = y ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3475 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3475 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3475.models_iff G M).mp hM
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
        have b1e48 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e50 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e48
        have b1e51 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e50
             have r₂ := b1e23
             grind)
          | exact resolve b1e50 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e52 : (σ x) = (σ (k x y)) := by
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
        have b1e53 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e52
          | exact resolve b1e52 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e52
        have b1e54 : False := by grind
        exact b1e54
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
        have b2e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e265 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e50 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50
        have b2e1485 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e265 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e265
          | (have j0 := b2e265 x y
             grind)
          | exact resolve b2e265 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e265
        have b2e1492 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e1485
        have b2e1498 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1492
             have r₂ := b2e22
             grind)
          | exact resolve b2e1492 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1492
        have b2e1502 : False := by grind
        exact b2e1502
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
        have b3e46 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
        have b3e49 : x = y ∨ x = (k x y) := by grind
        clear b3e46
        have b3e50 : x = (k x y) := by
          first
          | (have r₁ := b3e49
             have r₂ := b3e23
             grind)
          | exact resolve b3e49 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e49
        have b3e53 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e29
          | exact resolve b3e29 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e50
        have b3e54 : False := by grind
        exact b3e54
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
          have b5e42 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e46 : x = y ∨ x = (k x y) := by grind
          clear b5e42
          have b5e47 : x = (k x y) := by
            first
            | (have r₁ := b5e46
               have r₂ := b5e25
               grind)
            | exact resolve b5e46 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e46
          have b5e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e253 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e50 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e1620 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e253 x y
               have i₂ := b5e47
               grind)
            | exact superpose b5e47 b5e253
            | (have j0 := b5e253 x y
               grind)
            | exact resolve b5e253 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e253
          have b5e1625 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e1620
          have b5e1630 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1625
               have r₂ := b5e24
               grind)
            | exact resolve b5e1625 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1625
          have b5e1634 : False := by grind
          exact b5e1634
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
        have b6e52 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
        have b6e54 : y = (M.op x y) ∨ x = (M.op x y) := by grind
        clear b6e52
        have b6e57 : x = (M.op x y) := by
          first
          | (have r₁ := b6e54
             have r₂ := b6e21
             grind)
          | exact resolve b6e54 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e60 : False := by grind
        exact b6e60
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
          have b7e40 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e43 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e40
          have b7e44 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e43
               have r₂ := b7e25
               grind)
            | exact resolve b7e43 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e43
          have b7e45 : (σ x) = (σ (k x y)) := by
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
          have b7e48 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e14
            | exact resolve b7e14 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e49 : x = (k x y) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e48
            | exact resolve b7e48 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e59 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e49
               grind)
            | exact superpose b7e49 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e60 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b7e59
          have b7e62 : y = (M.op x y) := by
            first
            | (have r₁ := b7e60
               have r₂ := b7e21
               grind)
            | exact resolve b7e60 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e64 : False := by grind
          exact b7e64
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
          have b8e47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e253 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e47 x y
               grind)
            | exact superpose b8e47 b8e20
            | (have j1 := b8e47 x y
               grind)
            | exact resolve b8e20 b8e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47
          have b8e277 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e253
               have r₂ := b8e24
               grind)
            | exact resolve b8e253 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e253
          have b8e280 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e277
               have r₂ := b8e23
               grind)
            | exact resolve b8e277 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e277
          have b8e281 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e280
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e280
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e280 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e280
          have b8e282 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e281
          have b8e283 : x = (M.op x y) := by
            first
            | (have r₁ := b8e282
               have r₂ := b8e22
               grind)
            | exact resolve b8e282 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e282
          have b8e284 : False := by grind
          exact b8e284

/-- `Equation3475`: `x ◇ x = y ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation3475 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3475 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3475.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e60 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e63 : False := by grind
      exact b0e63
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
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
          have b4e33 : (M.op y y) = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b4e13 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b4e13 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e34
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e34
            | exact resolve b4e34 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e38 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e33
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e33
            | exact resolve b4e33 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e39 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e37
               have i₂ := b4e30 y
               grind)
            | exact superpose b4e30 b4e37
            | exact resolve b4e37 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e37
          have b4e85 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e39
               grind)
            | exact superpose b4e39 b4e20
            | exact resolve b4e20 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e90 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e85
               have i₂ := b4e38
               grind)
            | exact superpose b4e38 b4e85
            | exact resolve b4e85 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38 b4e85
          have b4e91 : False := by grind
          exact b4e91
        · have b5e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e33 : (M.op y y) = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b5e13 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b5e33
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e33
            | exact resolve b5e33 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e53 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b5e26
          have b5e58 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e53 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e53
            | exact resolve b5e53 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e59 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b5e58
          have b5e160 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (M.op (M.op (τ X1) X0) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e59 X1
               have i₂ := b5e13 (τ X1) X0
               grind)
            | exact superpose b5e13 b5e59
            | exact resolve b5e59 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e244 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b5e256 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e244
               have r₂ := b5e23
               grind)
            | exact resolve b5e244 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e244
          have b5e263 : (σ (k y x)) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e256
               have i₂ := b5e36
               grind)
            | exact superpose b5e36 b5e256
            | exact resolve b5e256 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e256
          have b5e406 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (M.op X0 (M.op (M.op (τ (σ X1)) X0) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e30 X1
               have i₂ := b5e160 X0 (σ X1)
               grind)
            | exact superpose b5e160 b5e30
            | exact resolve b5e30 b5e160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e160
          have b5e422 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (M.op X0 (M.op (M.op X1 X0) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e406 X0 X1
               have i₂ := b5e14 X1
               grind)
            | exact superpose b5e14 b5e406
            | exact resolve b5e406 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e406
          have b5e911 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b5e263
               have i₂ := b5e18 y x
               grind)
            | exact superpose b5e18 b5e263
            | (have j1 := b5e18 y x
               grind)
            | (have r₁ := b5e263
               have r₂ := b5e18 (σ (k y x)) (σ (M.op y y))
               grind)
            | (have r₁ := b5e263
               have r₂ := b5e18 (σ (M.op y y)) (σ (k y x))
               grind)
            | exact resolve b5e263 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e263
          have b5e912 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b5e911
               have r₂ := b5e21
               grind)
            | exact resolve b5e911 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e911
          have b5e913 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e912
               have i₂ := b5e36
               grind)
            | exact superpose b5e36 b5e912
            | exact resolve b5e912 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e912
          have b5e914 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b5e913
          have b5e915 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b5e914
               have i₂ := b5e36
               grind)
            | exact superpose b5e36 b5e914
            | exact resolve b5e914 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e914
          have b5e917 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e915
               grind)
            | exact superpose b5e915 b5e20
            | exact resolve b5e20 b5e915
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e921 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b5e17 (σ y) (σ x)
               have i₂ := b5e915
               grind)
            | exact superpose b5e915 b5e17
            | (have j0 := b5e17 (σ x) (σ y)
               grind)
            | (have r₁ := b5e17 (σ y) (σ x)
               have r₂ := b5e915
               grind)
            | exact resolve b5e17 b5e915
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e915
          have b5e928 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by grind
          clear b5e921
          have b5e934 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b5e928
               have r₂ := b5e23
               grind)
            | exact resolve b5e928 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e928
          have b5e938 : (σ x) ≠ (σ (M.op y y)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b5e917
               have i₂ := b5e36
               grind)
            | exact superpose b5e36 b5e917
            | exact resolve b5e917 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e917
          have b5e945 : (σ x) = (σ (k y x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b5e934
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e934
            | exact resolve b5e934 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e934
          have b5e1281 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b5e945
               have i₂ := b5e18 y x
               grind)
            | exact superpose b5e18 b5e945
            | (have j1 := b5e18 y x
               grind)
            | exact resolve b5e945 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e945
          have b5e1320 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b5e1281
               have r₂ := b5e21
               grind)
            | exact resolve b5e1281 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1281
          have b5e1326 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e1320
               have i₂ := b5e36
               grind)
            | exact superpose b5e36 b5e1320
            | exact resolve b5e1320 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1320
          have b5e1329 : x = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b5e1326
               have r₂ := b5e938
               grind)
            | exact resolve b5e1326 b5e938
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e938 b5e1326
          have b5e1331 : x = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b5e1329
               have i₂ := b5e36
               grind)
            | exact superpose b5e36 b5e1329
            | exact resolve b5e1329 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1329
          have b5e1332 : x = (M.op y y) := by grind
          clear b5e1331
          have b5e1444 : (σ x) = (σ (M.op y (M.op x y))) := by
            first
            | (have i₁ := b5e422 y y
               have i₂ := b5e1332
               grind)
            | exact superpose b5e1332 b5e422
            | exact resolve b5e422 b5e1332
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e422
          have b5e1448 : (σ x) = (σ (M.op y (M.op y y))) := by
            first
            | (have i₁ := b5e1444
               have i₂ := b5e36
               grind)
            | exact superpose b5e36 b5e1444
            | exact resolve b5e1444 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e1444
          have b5e1459 : (σ x) = (σ (M.op y x)) := by
            first
            | (have i₁ := b5e1448
               have i₂ := b5e1332
               grind)
            | exact superpose b5e1332 b5e1448
            | exact resolve b5e1448 b5e1332
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1332 b5e1448
          have b5e1469 : (σ x) = (σ y) := by
            first
            | (have i₁ := b5e1459
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1459
            | exact resolve b5e1459 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1459
          have b5e1477 : False := by grind
          exact b5e1477
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
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
          have b7e45 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e47 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e45
          have b7e48 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e47
               have r₂ := b7e23
               grind)
            | exact resolve b7e47 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
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
          have b7e63 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = y := by
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
          have b7e64 : y = (M.op y x) ∨ x = y := by grind
          clear b7e63
          have b7e66 : x = y := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e22
               grind)
            | exact resolve b7e64 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e68 : False := by grind
          exact b7e68
        · have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e56 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e196 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e208 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e196
               have r₂ := b8e23
               grind)
            | exact resolve b8e196 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e196
          have b8e989 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e208
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e208
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e208
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e208
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e208 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e990 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e989
          have b8e991 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e990
               have r₂ := b8e21
               grind)
            | exact resolve b8e990 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e990
          have b8e993 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e991
               grind)
            | exact superpose b8e991 b8e20
            | exact resolve b8e20 b8e991
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e997 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e991
               grind)
            | exact superpose b8e991 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e991
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e991
               grind)
            | exact resolve b8e17 b8e991
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e991
          have b8e1005 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e997
          have b8e1012 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e1005
               have r₂ := b8e23
               grind)
            | exact resolve b8e1005 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1005
          have b8e1020 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1012
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e1012
            | exact resolve b8e1012 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1012
          have b8e1350 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e1020
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e1020
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e1020 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1020
          have b8e1372 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e1350
          have b8e1390 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b8e1372
               have r₂ := b8e993
               grind)
            | exact resolve b8e1372 b8e993
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e993 b8e1372
          have b8e1393 : x = (M.op x y) := by
            first
            | (have r₁ := b8e1390
               have r₂ := b8e21
               grind)
            | exact resolve b8e1390 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1390
          have b8e1431 : x ≠ x ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e1393
               grind)
            | exact superpose b8e1393 b8e17
            | (have j0 := b8e17 x y
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e1393
               grind)
            | exact resolve b8e17 b8e1393
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1440 : x = y ∨ x = (k y x) := by grind
          clear b8e1431
          have b8e1449 : x = (k y x) := by
            first
            | (have r₁ := b8e1440
               have r₂ := b8e21
               grind)
            | exact resolve b8e1440 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1440
          have b8e1514 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e208
               have i₂ := b8e1449
               grind)
            | exact superpose b8e1449 b8e208
            | exact resolve b8e208 b8e1449
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e208 b8e1449
          have b8e1518 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e1514
               have i₂ := b8e1393
               grind)
            | exact superpose b8e1393 b8e1514
            | exact resolve b8e1514 b8e1393
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1514
          have b8e1519 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e1518
          have b8e1895 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1519
               grind)
            | exact superpose b8e1519 b8e20
            | exact resolve b8e20 b8e1519
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1519
          have b8e1925 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e1895
               have i₂ := b8e1393
               grind)
            | exact superpose b8e1393 b8e1895
            | exact resolve b8e1895 b8e1393
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1393 b8e1895
          have b8e1926 : False := by grind
          exact b8e1926
