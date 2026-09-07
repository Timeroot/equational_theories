import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if X = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_y_y_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x y) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e22
        | exact resolve b0e22 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e24 : False := by grind
      exact b0e24
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
          intro X0 X1 X2
          grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e47 : ∀ X0 : G, (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 X0 (M.op X0 x)
             have i₂ := b1e12 X0 X0 x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e51 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e47 (σ x)
             grind)
          | exact superpose b1e47 b1e24
          | (have r₁ := b1e24
             have r₂ := b1e47 (σ x)
             grind)
          | exact resolve b1e24 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e47
        have b1e56 : False := by grind
        exact b1e56
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : x ≠ x ∨ y = (k x y) := by
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
        have b2e26 : y = (k x y) := by grind
        clear b2e25
        have b2e34 : ∀ X0 : G, (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 X0 (M.op X0 x)
             have i₂ := b2e12 X0 X0 x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e181 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (M.op X2 (σ (k X0 X1))))) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (σ X0) X2 (σ X1)
             have i₂ := b2e45 X0 X1
             grind)
          | exact superpose b2e45 b2e12
          | (have j1 := b2e45 X0 X1
             grind)
          | exact resolve b2e12 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e988 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ y)))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e181 x y X0
             have i₂ := b2e26
             grind)
          | exact superpose b2e26 b2e181
          | (have j0 := b2e181 x y x
             grind)
          | exact resolve b2e181 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e181
        have b2e1022 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have j0 := b2e988 X0
             grind)
          | (have r₁ := b2e988 X0
             have r₂ := b2e22
             grind)
          | exact resolve b2e988 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e988
        have b2e1028 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ y)))) := by
          intro X0
          first
          | (have j0 := b2e1022 X0
             grind)
          | (have r₁ := b2e1022 X0
             have r₂ := b2e21
             grind)
          | exact resolve b2e1022 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1022
        have b2e1035 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
          first
          | (have i₁ := b2e1028 (σ y)
             have i₂ := b2e34 (σ y)
             grind)
          | exact superpose b2e34 b2e1028
          | exact resolve b2e1028 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e1028
        have b2e1106 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1035
             have i₂ := b2e45 x y
             grind)
          | exact superpose b2e45 b2e1035
          | (have j1 := b2e45 x y
             grind)
          | exact resolve b2e1035 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45 b2e1035
        have b2e1128 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1106
             have r₂ := b2e22
             grind)
          | exact resolve b2e1106 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1106
        have b2e1130 : (σ x) = (M.op (σ x) (σ (k x y))) := by
          first
          | (have r₁ := b2e1128
             have r₂ := b2e21
             grind)
          | exact resolve b2e1128 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1128
        have b2e1131 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1130
             have i₂ := b2e26
             grind)
          | exact superpose b2e26 b2e1130
          | exact resolve b2e1130 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e1130
        have b2e1132 : False := by grind
        exact b2e1132
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
          intro X0 X1 X2
          grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e50 : ∀ X0 : G, (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 X0 (M.op X0 x)
             have i₂ := b3e12 X0 X0 x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e55 : y ≠ y := by grind
        clear b3e50
        have b3e60 : False := by grind
        exact b3e60
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e22 : x = y := by grind
          have b4e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e42 : ∀ X0 : G, (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 X0 (M.op X0 x)
               have i₂ := b4e13 X0 X0 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e48 : (σ y) ≠ (σ y) := by grind
          clear b4e42
          have b4e53 : False := by grind
          exact b4e53
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b6e26 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b6e25
        have b6e27 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b6e26
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e26
          | exact resolve b6e26 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e32 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e27
             grind)
          | exact superpose b6e27 b6e13
          | exact resolve b6e13 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e33 : y = (k x y) := by
          first
          | (have i₁ := b6e32
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e32
          | exact resolve b6e32 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e41 : ∀ X0 : G, (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 X0 (M.op X0 x)
             have i₂ := b6e12 X0 X0 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e47 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 (M.op X0 X1) X1
             have i₂ := b6e41 (M.op X0 X1)
             grind)
          | exact superpose b6e41 b6e12
          | exact resolve b6e12 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e52 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e33
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e33
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e33 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e55 : y = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b6e52
             have r₂ := b6e21
             grind)
          | exact resolve b6e52 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e58 : y = (M.op x y) := by
          first
          | (have r₁ := b6e55
             have r₂ := b6e20
             grind)
          | exact resolve b6e55 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e122 : x = (M.op x (M.op x y)) := by
          first
          | (have i₁ := b6e47 x y
             have i₂ := b6e58
             grind)
          | exact superpose b6e58 b6e47
          | exact resolve b6e47 b6e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47
        have b6e133 : x = (M.op x y) := by
          first
          | (have i₁ := b6e122
             have i₂ := b6e58
             grind)
          | exact superpose b6e58 b6e122
          | exact resolve b6e122 b6e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58 b6e122
        have b6e140 : False := by grind
        exact b6e140
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e22 : x ≠ y := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : y = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e14
            | exact resolve b7e14 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : x = y := by
            first
            | (have i₁ := b7e28
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e28
            | exact resolve b7e28 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e30 : False := by grind
          exact b7e30
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x y) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e172 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
          have b8e180 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e172
               have r₂ := b8e24
               grind)
            | exact resolve b8e172 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e172
          have b8e183 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e180
               have r₂ := b8e23
               grind)
            | exact resolve b8e180 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e180
          have b8e184 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e183
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e183
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e183
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e183
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e183 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e183
          have b8e185 : x = y ∨ x = (M.op x y) := by grind
          clear b8e184
          have b8e186 : x = (M.op x y) := by
            first
            | (have r₁ := b8e185
               have r₂ := b8e22
               grind)
            | exact resolve b8e185 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e185
          have b8e187 : False := by grind
          exact b8e187

/-- `Equation4277`: `x ◇ (x ◇ x) = y ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pxx_y_pxy_Equation4277 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4277 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4277.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = b :=
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
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x y) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e22
        | exact resolve b0e22 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e24 : False := by grind
      exact b0e24
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e31 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (σ x) X0 X1
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = y := by
          intro X0
          first
          | (have i₁ := b1e34 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e34
          | exact resolve b1e34 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e44 : ∀ X1 X2 : G, (M.op X1 (M.op X1 X2)) = y := by
          intro X1 X2
          first
          | (have i₁ := b1e12 x X1 X2
             have i₂ := b1e40 x
             grind)
          | exact superpose b1e40 b1e12
          | exact resolve b1e12 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e46 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 (M.op X1 X1)
             have i₂ := b1e40 X1
             grind)
          | exact superpose b1e40 b1e12
          | exact resolve b1e12 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e47 : ∀ X1 : G, y = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b1e46 x X1
             have i₂ := b1e40 x
             grind)
          | exact superpose b1e40 b1e46
          | exact resolve b1e46 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e52 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 X2) ∨ (M.op X1 X1) = (k X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e15 X1 (M.op X1 X2)
             have i₂ := b1e12 X0 X1 X2
             grind)
          | (have i₁ := b1e15 X0 (M.op X0 X0)
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e15
          | (have j0 := b1e15 X1 (M.op X1 X2)
             grind)
          | (have r₁ := b1e15 X0 (M.op X0 (M.op X0 X0))
             have r₂ := b1e12 X0 X0 (M.op X0 X0)
             grind)
          | exact resolve b1e15 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e54 : ∀ X1 X2 : G, (M.op X1 X2) ≠ y ∨ (M.op X1 X1) = (k X1 (M.op X1 X2)) := by
          intro X1 X2
          first
          | (have i₁ := b1e52 x X1 X2
             have i₂ := b1e40 x
             grind)
          | exact superpose b1e40 b1e52
          | (have j0 := b1e52 x X1 X2
             grind)
          | exact resolve b1e52 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40 b1e52
        have b1e59 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 y
             have i₂ := b1e47 X0
             grind)
          | exact superpose b1e47 b1e15
          | (have j0 := b1e15 X0 y
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e47 x
             grind)
          | exact resolve b1e15 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e61 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e59 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b1e77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X0) y) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e67 X0 X1
             have i₂ := b1e61 (σ X0)
             grind)
          | exact superpose b1e61 b1e67
          | (have j0 := b1e67 X0 X1
             grind)
          | exact resolve b1e67 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67
        have b1e127 : ∀ X0 X1 : G, (σ y) ≠ (M.op X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e21
             have i₂ := b1e31 X0 X1
             grind)
          | exact superpose b1e31 b1e21
          | exact resolve b1e21 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e138 : y ≠ (σ y) := by
          first
          | (have i₁ := b1e127 x x
             have i₂ := b1e44 x x
             grind)
          | exact superpose b1e44 b1e127
          | exact resolve b1e127 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e127
        have b1e343 : ∀ X0 : G, (k X0 y) = (k X0 (k X0 y)) ∨ (k X0 y) = (M.op X0 (k X0 y)) := by
          intro X0
          grind
        have b1e347 : ∀ X0 : G, y = (M.op X0 (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e44 X0 X0
             have i₂ := b1e61 X0
             grind)
          | exact superpose b1e61 b1e44
          | exact resolve b1e44 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e359 : ∀ X0 : G, (k X0 y) = (k X0 (k X0 y)) ∨ y = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b1e343 X0
             have i₂ := b1e347 X0
             grind)
          | exact superpose b1e347 b1e343
          | (have j0 := b1e343 X0
             grind)
          | exact resolve b1e343 b1e347
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e343
        have b1e806 : ∀ X0 : G, y ≠ (k X0 y) ∨ (k X0 y) = (k X0 (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e54 X0 X0
             have i₂ := b1e61 X0
             grind)
          | exact superpose b1e61 b1e54
          | exact resolve b1e54 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e839 : ∀ X0 : G, (k X0 y) = (k X0 (k X0 y)) := by
          intro X0
          first
          | (have j0 := b1e806 X0
             have j1 := b1e359 X0
             grind)
          | (have r₁ := b1e806 X0
             have r₂ := b1e359 X0
             grind)
          | exact resolve b1e806 b1e359
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e359 b1e806
        have b1e875 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e839 X0
             have i₂ := b1e61 X0
             grind)
          | exact superpose b1e61 b1e839
          | exact resolve b1e839 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e977 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (k (σ X0) y) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e15 (σ X0) (σ X1)
             have i₂ := b1e77 X0 X1
             grind)
          | exact superpose b1e77 b1e15
          | (have j0 := b1e15 (σ X0) (σ X1)
             have j1 := b1e77 X0 X1
             grind)
          | (have r₁ := b1e15 (σ X0) (σ X1)
             have r₂ := b1e77 X0 X1
             grind)
          | exact resolve b1e15 b1e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e77
        have b1e991 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (k (σ X0) y) := by
          intro X0 X1
          first
          | (have j0 := b1e977 X0 X1
             have j1 := b1e15 (σ X0) (σ X1)
             grind)
          | (have r₁ := b1e977 X0 X1
             have r₂ := b1e15 (σ X0) (σ X1)
             grind)
          | exact resolve b1e977 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e977
        have b1e1011 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (k (σ X0) y) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (k (σ X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b1e991 X0 X1
             have i₂ := b1e61 (σ X0)
             grind)
          | exact superpose b1e61 b1e991
          | (have j0 := b1e991 X0 X1
             grind)
          | exact resolve b1e991 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e991
        have b1e1020 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (k (σ X0) y) ∨ (σ X1) = (k (σ X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b1e1011 X0 X1
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e1011
          | (have j0 := b1e1011 X0 X1
             grind)
          | exact resolve b1e1011 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1011
        have b1e2702 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) y) = (σ (M.op X0 X0)) ∨ (k (σ X0) y) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e1020 X0 (M.op X0 X0)
             have i₂ := b1e875 X0
             grind)
          | exact superpose b1e875 b1e1020
          | (have j0 := b1e1020 X0 (M.op X0 X0)
             grind)
          | exact resolve b1e1020 b1e875
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e875
        have b1e2705 : ∀ X0 : G, (σ (k X0 y)) ≠ (σ (k X0 y)) ∨ (k (σ X0) y) = (σ (k X0 y)) ∨ (k (σ X0) y) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e1020 X0 (k X0 y)
             have i₂ := b1e839 X0
             grind)
          | exact superpose b1e839 b1e1020
          | (have j0 := b1e1020 X0 y
             grind)
          | exact resolve b1e1020 b1e839
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e839 b1e1020
        have b1e2738 : ∀ X0 : G, (σ (k X0 y)) ≠ (σ (k X0 y)) ∨ (k (σ X0) y) = (σ (k X0 y)) := by
          intro X0
          first
          | (have j0 := b1e2705 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2705
        have b1e2739 : ∀ X0 : G, (k (σ X0) y) = (σ (k X0 y)) := by
          intro X0
          first
          | (have j0 := b1e2738 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2738
        have b1e2744 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) y) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b1e2702 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2702
        have b1e2745 : ∀ X0 : G, (k (σ X0) y) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b1e2744 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2744
        have b1e3164 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e2739 X0
             have i₂ := b1e2745 X0
             grind)
          | exact superpose b1e2745 b1e2739
          | exact resolve b1e2739 b1e2745
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e3169 : ∀ X0 : G, y = (M.op (σ X0) (σ (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b1e347 (σ X0)
             have i₂ := b1e2745 X0
             grind)
          | exact superpose b1e2745 b1e347
          | exact resolve b1e347 b1e2745
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e347 b1e2745
        have b1e7070 : y = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e3169 y
             have i₂ := b1e47 y
             grind)
          | exact superpose b1e47 b1e3169
          | exact resolve b1e3169 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3169
        have b1e7120 : y = (k (σ y) y) := by
          first
          | (have i₁ := b1e7070
             have i₂ := b1e61 (σ y)
             grind)
          | exact superpose b1e61 b1e7070
          | exact resolve b1e7070 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61 b1e7070
        have b1e7159 : y = (σ (k y y)) := by
          first
          | (have i₁ := b1e7120
             have i₂ := b1e2739 y
             grind)
          | exact superpose b1e2739 b1e7120
          | exact resolve b1e7120 b1e2739
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2739 b1e7120
        have b1e7185 : y = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e7159
             have i₂ := b1e3164 y
             grind)
          | exact superpose b1e3164 b1e7159
          | exact resolve b1e7159 b1e3164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3164 b1e7159
        have b1e7197 : y = (σ y) := by
          first
          | (have i₁ := b1e7185
             have i₂ := b1e47 y
             grind)
          | exact superpose b1e47 b1e7185
          | exact resolve b1e7185 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47 b1e7185
        have b1e7201 : False := by grind
        exact b1e7201
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e33 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
          intro X0
          first
          | (have i₁ := b2e12 X0 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = y := by
          intro X0
          first
          | (have i₁ := b2e33 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e33
          | exact resolve b2e33 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e41 : ∀ X1 X2 : G, (M.op X1 (M.op X1 X2)) = y := by
          intro X1 X2
          first
          | (have i₁ := b2e12 x X1 X2
             have i₂ := b2e38 x
             grind)
          | exact superpose b2e38 b2e12
          | exact resolve b2e12 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e43 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 (M.op X1 X1)
             have i₂ := b2e38 X1
             grind)
          | exact superpose b2e38 b2e12
          | exact resolve b2e12 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e44 : ∀ X1 : G, y = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b2e43 x X1
             have i₂ := b2e38 x
             grind)
          | exact superpose b2e38 b2e43
          | exact resolve b2e43 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e43
        have b2e48 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 X2) ∨ (M.op X1 X1) = (k X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X1 (M.op X1 X2)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | (have i₁ := b2e15 X0 (M.op X0 X0)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 X1 (M.op X1 X2)
             grind)
          | (have r₁ := b2e15 X0 (M.op X0 (M.op X0 X0))
             have r₂ := b2e12 X0 X0 (M.op X0 X0)
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e50 : ∀ X1 X2 : G, (M.op X1 X2) ≠ y ∨ (M.op X1 X1) = (k X1 (M.op X1 X2)) := by
          intro X1 X2
          first
          | (have i₁ := b2e48 x X1 X2
             have i₂ := b2e38 x
             grind)
          | exact superpose b2e38 b2e48
          | (have j0 := b2e48 x X1 X2
             grind)
          | exact resolve b2e48 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e48
        have b2e54 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b2e15 X0 y
             have i₂ := b2e44 X0
             grind)
          | exact superpose b2e44 b2e15
          | (have j0 := b2e15 X0 y
             grind)
          | (have r₁ := b2e15 x y
             have r₂ := b2e44 x
             grind)
          | exact resolve b2e15 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e56 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b2e54 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54
        have b2e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X0) y) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e61 X0 X1
             have i₂ := b2e56 (σ X0)
             grind)
          | exact superpose b2e56 b2e61
          | (have j0 := b2e61 X0 X1
             grind)
          | exact resolve b2e61 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e111 : ∀ X0 : G, (k X0 y) = (k X0 (k X0 y)) ∨ (k X0 y) = (M.op X0 (k X0 y)) := by
          intro X0
          grind
        have b2e115 : ∀ X0 : G, y = (M.op X0 (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b2e41 X0 X0
             have i₂ := b2e56 X0
             grind)
          | exact superpose b2e56 b2e41
          | exact resolve b2e41 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e121 : ∀ X0 : G, (k X0 y) = (k X0 (k X0 y)) ∨ y = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b2e111 X0
             have i₂ := b2e115 X0
             grind)
          | exact superpose b2e115 b2e111
          | (have j0 := b2e111 X0
             grind)
          | exact resolve b2e111 b2e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e111
        have b2e549 : ∀ X0 : G, y ≠ (k X0 y) ∨ (k X0 y) = (k X0 (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b2e50 X0 X0
             have i₂ := b2e56 X0
             grind)
          | exact superpose b2e56 b2e50
          | exact resolve b2e50 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50
        have b2e576 : ∀ X0 : G, (k X0 y) = (k X0 (k X0 y)) := by
          intro X0
          first
          | (have j0 := b2e549 X0
             have j1 := b2e121 X0
             grind)
          | (have r₁ := b2e549 X0
             have r₂ := b2e121 X0
             grind)
          | exact resolve b2e549 b2e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e121 b2e549
        have b2e589 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e576 X0
             have i₂ := b2e56 X0
             grind)
          | exact superpose b2e56 b2e576
          | exact resolve b2e576 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e683 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (k (σ X0) y) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 (σ X0) (σ X1)
             have i₂ := b2e71 X0 X1
             grind)
          | exact superpose b2e71 b2e15
          | (have j0 := b2e15 (σ X0) (σ X1)
             have j1 := b2e71 X0 X1
             grind)
          | (have r₁ := b2e15 (σ X0) (σ X1)
             have r₂ := b2e71 X0 X1
             grind)
          | exact resolve b2e15 b2e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71
        have b2e695 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (k (σ X0) y) := by
          intro X0 X1
          first
          | (have j0 := b2e683 X0 X1
             have j1 := b2e15 (σ X0) (σ X1)
             grind)
          | (have r₁ := b2e683 X0 X1
             have r₂ := b2e15 (σ X0) (σ X1)
             grind)
          | exact resolve b2e683 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e683
        have b2e712 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (k (σ X0) y) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (k (σ X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b2e695 X0 X1
             have i₂ := b2e56 (σ X0)
             grind)
          | exact superpose b2e56 b2e695
          | (have j0 := b2e695 X0 X1
             grind)
          | exact resolve b2e695 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e695
        have b2e719 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (k (σ X0) y) ∨ (σ X1) = (k (σ X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b2e712 X0 X1
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e712
          | (have j0 := b2e712 X0 X1
             grind)
          | exact resolve b2e712 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e712
        have b2e2108 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) y) = (σ (M.op X0 X0)) ∨ (k (σ X0) y) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e719 X0 (M.op X0 X0)
             have i₂ := b2e589 X0
             grind)
          | exact superpose b2e589 b2e719
          | (have j0 := b2e719 X0 (M.op X0 X0)
             grind)
          | exact resolve b2e719 b2e589
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e589
        have b2e2111 : ∀ X0 : G, (σ (k X0 y)) ≠ (σ (k X0 y)) ∨ (k (σ X0) y) = (σ (k X0 y)) ∨ (k (σ X0) y) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b2e719 X0 (k X0 y)
             have i₂ := b2e576 X0
             grind)
          | exact superpose b2e576 b2e719
          | (have j0 := b2e719 X0 y
             grind)
          | exact resolve b2e719 b2e576
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e576 b2e719
        have b2e2144 : ∀ X0 : G, (σ (k X0 y)) ≠ (σ (k X0 y)) ∨ (k (σ X0) y) = (σ (k X0 y)) := by
          intro X0
          first
          | (have j0 := b2e2111 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2111
        have b2e2145 : ∀ X0 : G, (k (σ X0) y) = (σ (k X0 y)) := by
          intro X0
          first
          | (have j0 := b2e2144 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2144
        have b2e2150 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) y) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b2e2108 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2108
        have b2e2151 : ∀ X0 : G, (k (σ X0) y) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b2e2150 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2150
        have b2e2618 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e2145 X0
             have i₂ := b2e2151 X0
             grind)
          | exact superpose b2e2151 b2e2145
          | exact resolve b2e2145 b2e2151
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2622 : ∀ X0 : G, y = (M.op (σ X0) (σ (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b2e115 (σ X0)
             have i₂ := b2e2151 X0
             grind)
          | exact superpose b2e2151 b2e115
          | exact resolve b2e115 b2e2151
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e115 b2e2151
        have b2e5547 : y = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e2622 y
             have i₂ := b2e44 y
             grind)
          | exact superpose b2e44 b2e2622
          | exact resolve b2e2622 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2622
        have b2e5588 : y = (k (σ y) y) := by
          first
          | (have i₁ := b2e5547
             have i₂ := b2e56 (σ y)
             grind)
          | exact superpose b2e56 b2e5547
          | exact resolve b2e5547 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56 b2e5547
        have b2e5623 : y = (σ (k y y)) := by
          first
          | (have i₁ := b2e5588
             have i₂ := b2e2145 y
             grind)
          | exact superpose b2e2145 b2e5588
          | exact resolve b2e5588 b2e2145
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2145 b2e5588
        have b2e5645 : y = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e5623
             have i₂ := b2e2618 y
             grind)
          | exact superpose b2e2618 b2e5623
          | exact resolve b2e5623 b2e2618
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2618 b2e5623
        have b2e5654 : y = (σ y) := by
          first
          | (have i₁ := b2e5645
             have i₂ := b2e44 y
             grind)
          | exact superpose b2e44 b2e5645
          | exact resolve b2e5645 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5645
        have b2e6143 : y ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e5654
             grind)
          | exact superpose b2e5654 b2e21
          | exact resolve b2e21 b2e5654
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5654
        have b2e6185 : False := by grind
        exact b2e6185
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 x X0 X1
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X2)) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X2 X3 (M.op X3 X3)
             have i₂ := b3e12 X3 X0 X1
             grind)
          | (have i₁ := b3e12 X0 X1 (M.op X1 X2)
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e36 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e31 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e31
          | exact resolve b3e31 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e37 : (M.op x y) = (σ y) := by
          first
          | (have i₁ := b3e36 x
             have i₂ := b3e27 x x
             grind)
          | exact superpose b3e27 b3e36
          | exact resolve b3e36 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e39 : y ≠ (σ y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e37
             grind)
          | exact superpose b3e37 b3e20
          | exact resolve b3e20 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e82 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b3e27 X0 (M.op X0 x)
             have i₂ := b3e27 X0 x
             grind)
          | exact superpose b3e27 b3e27
          | exact resolve b3e27 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e95 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e82 X0
             have i₂ := b3e37
             grind)
          | exact superpose b3e37 b3e82
          | exact resolve b3e82 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e82
        have b3e123 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (σ y) X0 X1
             have i₂ := b3e95 (σ y)
             grind)
          | exact superpose b3e95 b3e12
          | exact resolve b3e12 b3e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e125 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e15 X0 (σ y)
             have i₂ := b3e95 X0
             grind)
          | exact superpose b3e95 b3e15
          | (have j0 := b3e15 X0 (σ y)
             grind)
          | (have r₁ := b3e15 X0 (σ y)
             have r₂ := b3e95 X0
             grind)
          | exact resolve b3e15 b3e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e127 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e125 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e125
        have b3e130 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e123 X0 X1
             have i₂ := b3e95 (σ y)
             grind)
          | exact superpose b3e95 b3e123
          | exact resolve b3e123 b3e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e123
        have b3e153 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e127 (σ X0)
             grind)
          | exact superpose b3e127 b3e18
          | exact resolve b3e18 b3e127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e127
        have b3e383 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e32 X1 X2 (σ y) X0
             have i₂ := b3e95 (σ y)
             grind)
          | exact superpose b3e95 b3e32
          | exact resolve b3e32 b3e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e508 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e383 X0 x x
             have i₂ := b3e27 x x
             grind)
          | exact superpose b3e27 b3e383
          | exact resolve b3e383 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e383
        have b3e564 : ∀ X0 : G, (M.op X0 (M.op x y)) = (σ (k y y)) := by
          intro X0
          first
          | (have i₁ := b3e508 X0
             have i₂ := b3e153 y
             grind)
          | exact superpose b3e153 b3e508
          | exact resolve b3e508 b3e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e153 b3e508
        have b3e599 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (k y y)) := by
          intro X0
          first
          | (have i₁ := b3e564 X0
             have i₂ := b3e37
             grind)
          | exact superpose b3e37 b3e564
          | exact resolve b3e564 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37 b3e564
        have b3e619 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e599 x
             have i₂ := b3e95 x
             grind)
          | exact superpose b3e95 b3e599
          | exact resolve b3e599 b3e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e95 b3e599
        have b3e633 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e619
             grind)
          | exact superpose b3e619 b3e13
          | exact resolve b3e13 b3e619
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e619
        have b3e635 : y = (k y y) := by
          first
          | (have i₁ := b3e633
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e633
          | exact resolve b3e633 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e633
        have b3e889 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e635
             grind)
          | exact superpose b3e635 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e635
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e635
        have b3e890 : y = (M.op y y) := by grind
        clear b3e889
        have b3e967 : (σ y) = (M.op y y) := by
          first
          | (have i₁ := b3e130 y y
             have i₂ := b3e890
             grind)
          | exact superpose b3e890 b3e130
          | exact resolve b3e130 b3e890
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e130
        have b3e969 : y = (σ y) := by
          first
          | (have i₁ := b3e967
             have i₂ := b3e890
             grind)
          | exact superpose b3e890 b3e967
          | exact resolve b3e967 b3e890
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e890 b3e967
        have b3e978 : False := by grind
        exact b3e978
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e32 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 x X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : (M.op x y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e32 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e32
            | exact resolve b4e32 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b4e32 X0 (M.op X0 x)
               have i₂ := b4e32 X0 x
               grind)
            | exact superpose b4e32 b4e32
            | exact resolve b4e32 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b4e107 : (M.op x y) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e42
               grind)
            | exact superpose b4e42 b4e20
            | exact resolve b4e20 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e319 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (k X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b4e16 X0 (M.op x y)
               have i₂ := b4e44 X0
               grind)
            | exact superpose b4e44 b4e16
            | (have j0 := b4e16 X0 (M.op x y)
               grind)
            | (have r₁ := b4e16 X0 (M.op x y)
               have r₂ := b4e44 X0
               grind)
            | exact resolve b4e16 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e322 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) := by
            intro X0
            first
            | (have j0 := b4e319 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e319
          have b4e340 : ∀ X0 : G, (M.op x y) = (M.op X0 (k X0 (M.op x y))) := by
            intro X0
            first
            | (have i₁ := b4e32 X0 X0
               have i₂ := b4e322 X0
               grind)
            | exact superpose b4e322 b4e32
            | exact resolve b4e32 b4e322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e966 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e65 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e65
          have b4e968 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e966 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e966
          have b4e1537 : (σ (M.op x y)) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e968 (M.op x y)
               have i₂ := b4e322 (M.op x y)
               grind)
            | exact superpose b4e322 b4e968
            | (have j0 := b4e968 (M.op x y)
               grind)
            | exact resolve b4e968 b4e322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e968
          have b4e1557 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e1537
               have i₂ := b4e44 (M.op x y)
               grind)
            | exact superpose b4e44 b4e1537
            | exact resolve b4e1537 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e1537
          have b4e1558 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
          clear b4e1557
          have b4e1566 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) := by
            first
            | (have i₁ := b4e1558
               have i₂ := b4e322 (σ (M.op x y))
               grind)
            | exact superpose b4e322 b4e1558
            | exact resolve b4e1558 b4e322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1558
          have b4e2158 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e340 (σ (M.op x y))
               have i₂ := b4e1566
               grind)
            | exact superpose b4e1566 b4e340
            | exact resolve b4e340 b4e1566
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e340
          have b4e2165 : (M.op x y) = (k (σ (M.op x y)) (M.op x y)) := by
            first
            | (have i₁ := b4e2158
               have i₂ := b4e322 (σ (M.op x y))
               grind)
            | exact superpose b4e322 b4e2158
            | exact resolve b4e2158 b4e322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e322 b4e2158
          have b4e2300 : (M.op x y) = (σ (M.op x y)) := by
            first
            | (have i₁ := b4e1566
               have i₂ := b4e2165
               grind)
            | exact superpose b4e2165 b4e1566
            | exact resolve b4e1566 b4e2165
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1566 b4e2165
          have b4e2318 : False := by grind
          exact b4e2318
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x y) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e61 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ x) X0
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 (σ x) X0
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e77 : y = (k x y) ∨ y = (M.op x y) := by grind
          have b5e82 : y = (k x y) := by
            first
            | (have r₁ := b5e77
               have r₂ := b5e21
               grind)
            | exact resolve b5e77 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77
          have b5e592 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e61 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e593 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e592
               have r₂ := b5e23
               grind)
            | exact resolve b5e592 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e592
          have b5e594 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e593
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e593
            | exact resolve b5e593 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e593
          have b5e595 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e594
               have i₂ := b5e82
               grind)
            | exact superpose b5e82 b5e594
            | exact resolve b5e594 b5e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e82 b5e594
          have b5e596 : False := by grind
          exact b5e596
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e29 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e30 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X2)) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X2 X3 (M.op X3 X3)
             have i₂ := b6e12 X3 X0 X1
             grind)
          | (have i₁ := b6e12 X0 X1 (M.op X1 X2)
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e34 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ y) := by
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
        have b6e37 : ∀ X1 X2 : G, (M.op X1 (M.op X1 X2)) = (σ y) := by
          intro X1 X2
          first
          | (have i₁ := b6e12 x X1 X2
             have i₂ := b6e34 x
             grind)
          | exact superpose b6e34 b6e12
          | exact resolve b6e12 b6e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e39 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 (M.op X1 X1)
             have i₂ := b6e34 X1
             grind)
          | exact superpose b6e34 b6e12
          | exact resolve b6e12 b6e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e40 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
          intro X1
          first
          | (have i₁ := b6e39 x X1
             have i₂ := b6e34 x
             grind)
          | exact superpose b6e34 b6e39
          | exact resolve b6e39 b6e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e51 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e15 X0 (σ y)
             have i₂ := b6e40 X0
             grind)
          | exact superpose b6e40 b6e15
          | (have j0 := b6e15 X0 (σ y)
             grind)
          | (have r₁ := b6e15 x (σ y)
             have r₂ := b6e40 x
             grind)
          | exact resolve b6e15 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e51 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e291 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X1 (M.op X1 X2)) (σ y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e53 (M.op X1 (M.op X1 X2))
             have i₂ := b6e30 X1 X2 X0 (M.op X1 (M.op X1 X2))
             grind)
          | exact superpose b6e30 b6e53
          | exact resolve b6e53 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e308 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e291 X0 x x
             have i₂ := b6e37 x x
             grind)
          | exact superpose b6e37 b6e291
          | exact resolve b6e291 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e291
        have b6e354 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (k y y)) := by
          intro X0
          first
          | (have i₁ := b6e308 X0
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e308
          | exact resolve b6e308 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e308
        have b6e389 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e354 x
             have i₂ := b6e34 x
             grind)
          | exact superpose b6e34 b6e354
          | exact resolve b6e354 b6e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e354
        have b6e410 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e389
             grind)
          | exact superpose b6e389 b6e13
          | exact resolve b6e13 b6e389
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e389
        have b6e412 : y = (k y y) := by
          first
          | (have i₁ := b6e410
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e410
          | exact resolve b6e410 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e410
        have b6e595 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e412
             grind)
          | exact superpose b6e412 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e412
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e412
        have b6e596 : y = (M.op y y) := by grind
        clear b6e595
        have b6e650 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op y y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e30 y y X0 X1
             have i₂ := b6e596
             grind)
          | exact superpose b6e596 b6e30
          | exact resolve b6e30 b6e596
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e651 : (σ y) = (M.op y y) := by
          first
          | (have i₁ := b6e37 y y
             have i₂ := b6e596
             grind)
          | exact superpose b6e596 b6e37
          | exact resolve b6e37 b6e596
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e654 : y = (σ y) := by
          first
          | (have i₁ := b6e651
             have i₂ := b6e596
             grind)
          | exact superpose b6e596 b6e651
          | exact resolve b6e651 b6e596
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e651
        have b6e655 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b6e650 X0 X1
             have i₂ := b6e596
             grind)
          | exact superpose b6e596 b6e650
          | exact resolve b6e650 b6e596
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e596 b6e650
        have b6e662 : ∀ X1 : G, (σ y) = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b6e655 x X1
             have i₂ := b6e34 x
             grind)
          | exact superpose b6e34 b6e655
          | exact resolve b6e655 b6e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34 b6e655
        have b6e664 : ∀ X1 : G, y = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b6e662 X1
             have i₂ := b6e654
             grind)
          | exact superpose b6e654 b6e662
          | exact resolve b6e662 b6e654
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e654 b6e662
        have b6e955 : y ≠ y := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e664 x
             grind)
          | exact superpose b6e664 b6e20
          | (have r₁ := b6e20
             have r₂ := b6e664 x
             grind)
          | exact resolve b6e20 b6e664
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e664
        have b6e956 : False := by grind
        exact b6e956
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x y) := by grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e84 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          have b7e91 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e84
               have r₂ := b7e23
               grind)
            | exact resolve b7e84 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84
          have b7e92 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e91
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e91
            | exact resolve b7e91 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e98 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e92
               grind)
            | exact superpose b7e92 b7e14
            | exact resolve b7e14 b7e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
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
          have b7e126 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
          have b7e127 : y = (M.op x y) ∨ y = (M.op x x) := by grind
          clear b7e126
          have b7e129 : y = (M.op x x) := by
            first
            | (have r₁ := b7e127
               have r₂ := b7e21
               grind)
            | exact resolve b7e127 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e127
          have b7e131 : False := by grind
          exact b7e131
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x y) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e62 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e594 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e62 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e595 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e594
               have r₂ := b8e23
               grind)
            | exact resolve b8e594 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e594
          have b8e596 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e595
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e595
            | exact resolve b8e595 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e595
          have b8e597 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e596
               grind)
            | exact superpose b8e596 b8e20
            | exact resolve b8e20 b8e596
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e596
          have b8e937 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e597
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e597
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e597 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e597
          have b8e938 : y = (M.op x x) ∨ y = (M.op x y) := by grind
          clear b8e937
          have b8e940 : y = (M.op x y) := by
            first
            | (have r₁ := b8e938
               have r₂ := b8e22
               grind)
            | exact resolve b8e938 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e938
          have b8e942 : False := by grind
          exact b8e942

/-- `Equation4279`: `x ◇ (x ◇ x) = y ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_y_y_pxy_Equation4279 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4279 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4279.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = b :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 X1)) := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
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
      have b0e33 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ x) X0 X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 (M.op X2 X3) X3
           have i₂ := b0e11 X0 X3 X2
           grind)
        | (have i₁ := b0e11 X0 (M.op X0 X0) X0
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
      have b0e606 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X1 (M.op X1 X1)) (M.op X0 (M.op X0 X0))) := by
        intro X0 X1
        grind
      clear b0e39
      have b0e628 : ∀ X1 : G, (M.op x y) = (k (M.op X1 (M.op X1 X1)) (M.op x y)) := by
        intro X1
        first
        | (have i₁ := b0e606 x X1
           have i₂ := b0e36 x
           grind)
        | exact superpose b0e36 b0e606
        | exact resolve b0e606 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e606
      have b0e683 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
        first
        | (have i₁ := b0e628 x
           have i₂ := b0e36 x
           grind)
        | exact superpose b0e36 b0e628
        | exact resolve b0e628 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e628
      have b0e945 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e74 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74
      have b0e946 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e945 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e945
      have b0e1324 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e946 (M.op x y)
           have i₂ := b0e683
           grind)
        | exact superpose b0e683 b0e946
        | (have j0 := b0e946 (M.op x y)
           grind)
        | exact resolve b0e946 b0e683
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e683 b0e946
      have b0e1333 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
      clear b0e1324
      have b0e1461 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e33 (σ (M.op x y)) (σ (M.op x y))
           have i₂ := b0e1333
           grind)
        | exact superpose b0e1333 b0e33
        | exact resolve b0e33 b0e1333
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e1472 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e1461
           have i₂ := b0e1333
           grind)
        | exact superpose b0e1333 b0e1461
        | exact resolve b0e1461 b0e1333
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1333 b0e1461
      have b0e1485 : False := by grind
      exact b0e1485
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 X1)) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
        have b1e27 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 x X0 X1
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : (M.op x y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e27 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e27
          | exact resolve b1e27 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b1e80 : (M.op x y) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e36
             grind)
          | exact superpose b1e36 b1e19
          | exact resolve b1e19 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e745 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e70 x x
             grind)
          | exact superpose b1e70 b1e21
          | (have j1 := b1e70 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e70 x y
             grind)
          | exact resolve b1e21 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70
        have b1e813 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e745
        have b1e1128 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e813
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e813
          | (have j1 := b1e17 (σ x) (σ x)
             grind)
          | exact resolve b1e813 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e813
        have b1e1129 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e1128
        have b1e1130 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e1129
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1129
          | exact resolve b1e1129 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1129
        have b1e1131 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e1130
        have b1e1137 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e1131
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1131
          | exact resolve b1e1131 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1131
        have b1e1194 : (σ x) ≠ (σ y) ∨ x = y := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e1137
             grind)
          | exact superpose b1e1137 b1e21
          | exact resolve b1e21 b1e1137
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1198 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by grind
        clear b1e1137
        have b1e1219 : (σ x) = (σ (k x x)) ∨ x = y := by
          first
          | (have i₁ := b1e1198
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e1198
          | exact resolve b1e1198 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1198
        have b1e1338 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e1219
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e1219
          | (have j1 := b1e17 x x
             grind)
          | exact resolve b1e1219 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1219
        have b1e1362 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) := by grind
        clear b1e1338
        have b1e1376 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e1362
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1362
          | exact resolve b1e1362 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1362
        have b1e1381 : x = y ∨ x = (M.op x x) := by
          first
          | (have r₁ := b1e1376
             have r₂ := b1e1194
             grind)
          | exact resolve b1e1376 b1e1194
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1194 b1e1376
        have b1e1386 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e1381
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1381
          | exact resolve b1e1381 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1381
        have b1e1387 : x = y := by grind
        clear b1e1386
        have b1e1470 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e1387
             grind)
          | exact superpose b1e1387 b1e22
          | exact resolve b1e22 b1e1387
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1472 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e31 X0
             have i₂ := b1e1387
             grind)
          | exact superpose b1e1387 b1e31
          | exact resolve b1e31 b1e1387
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e1476 : (M.op x x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e80
             have i₂ := b1e1387
             grind)
          | exact superpose b1e1387 b1e80
          | exact resolve b1e80 b1e1387
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80
        have b1e1483 : y ≠ (σ y) := by
          first
          | (have i₁ := b1e1476
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1476
          | exact resolve b1e1476 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1476
        have b1e1486 : (M.op x y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e1472 x
             have i₂ := b1e30 x
             grind)
          | exact superpose b1e30 b1e1472
          | exact resolve b1e1472 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e1472
        have b1e1491 : x ≠ (σ x) := by
          first
          | (have i₁ := b1e1483
             have i₂ := b1e1387
             grind)
          | exact superpose b1e1387 b1e1483
          | exact resolve b1e1483 b1e1387
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1483
        have b1e1494 : (M.op x y) = (σ x) := by
          first
          | (have i₁ := b1e1486
             have i₂ := b1e1470
             grind)
          | exact superpose b1e1470 b1e1486
          | exact resolve b1e1486 b1e1470
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1470 b1e1486
        have b1e1495 : (σ x) = (M.op x x) := by
          first
          | (have i₁ := b1e1494
             have i₂ := b1e1387
             grind)
          | exact superpose b1e1387 b1e1494
          | exact resolve b1e1494 b1e1387
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1494
        have b1e1496 : y = (σ x) := by
          first
          | (have i₁ := b1e1495
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1495
          | exact resolve b1e1495 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1495
        have b1e1497 : x = (σ x) := by
          first
          | (have i₁ := b1e1496
             have i₂ := b1e1387
             grind)
          | exact superpose b1e1387 b1e1496
          | exact resolve b1e1496 b1e1387
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1387 b1e1496
        have b1e1498 : False := by grind
        exact b1e1498
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
        have b2e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b2e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
        have b2e558 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e65 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e559 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e558
             have r₂ := b2e22
             grind)
          | exact resolve b2e558 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e558
        have b2e560 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e559
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e559
          | exact resolve b2e559 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e559
        have b2e561 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e560
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e560
          | exact resolve b2e560 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e560
        have b2e613 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e64 x x
             grind)
          | exact superpose b2e64 b2e21
          | (have j1 := b2e64 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e64 x y
             grind)
          | exact resolve b2e21 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e679 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e613
        have b2e1117 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e679
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e679
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e679 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e679
        have b2e1118 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e1117
        have b2e1119 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e1118
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1118
          | exact resolve b2e1118 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1118
        have b2e1120 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e1119
        have b2e1126 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e1120
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1120
          | exact resolve b2e1120 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1120
        have b2e1190 : (σ x) ≠ (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e1126
             grind)
          | exact superpose b2e1126 b2e21
          | exact resolve b2e21 b2e1126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1194 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by grind
        clear b2e1126
        have b2e1213 : (σ x) = (σ (k x x)) ∨ x = y := by
          first
          | (have i₁ := b2e1194
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e1194
          | exact resolve b2e1194 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1194
        have b2e1334 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e1213
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e1213
          | (have j1 := b2e17 x x
             grind)
          | exact resolve b2e1213 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1213
        have b2e1358 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) := by grind
        clear b2e1334
        have b2e1372 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e1358
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1358
          | exact resolve b2e1358 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1358
        have b2e1377 : x = y ∨ x = (M.op x x) := by
          first
          | (have r₁ := b2e1372
             have r₂ := b2e1190
             grind)
          | exact resolve b2e1372 b2e1190
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1190 b2e1372
        have b2e1382 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e1377
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1377
          | exact resolve b2e1377 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1377
        have b2e1383 : x = y := by grind
        clear b2e1382
        have b2e1467 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e1383
             grind)
          | exact superpose b2e1383 b2e22
          | exact resolve b2e22 b2e1383
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1472 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e561
             have i₂ := b2e1383
             grind)
          | exact superpose b2e1383 b2e561
          | exact resolve b2e561 b2e1383
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e561 b2e1383
        have b2e1491 : False := by grind
        exact b2e1491
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b3e917 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e72 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e72
          | exact resolve b3e72 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72
        have b3e998 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e917
        have b3e1067 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e998
             grind)
          | exact superpose b3e998 b3e13
          | exact resolve b3e13 b3e998
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1082 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1067
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e1067
          | exact resolve b3e1067 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1067
        have b3e1134 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e1082
             grind)
          | exact superpose b3e1082 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e1082
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1082
        have b3e1135 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b3e1134
        have b3e1137 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e1135
             have r₂ := b3e20
             grind)
          | exact resolve b3e1135 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1135
        have b3e1188 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e1137
        have b3e1315 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e998
             have i₂ := b3e1188
             grind)
          | exact superpose b3e1188 b3e998
          | exact resolve b3e998 b3e1188
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e998 b3e1188
        have b3e1322 : (σ x) = (σ y) := by grind
        clear b3e1315
        have b3e1391 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e1322
             grind)
          | exact superpose b3e1322 b3e13
          | exact resolve b3e13 b3e1322
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1322
        have b3e1424 : x = y := by
          first
          | (have i₁ := b3e1391
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e1391
          | exact resolve b3e1391 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1391
        have b3e1538 : x = (M.op x x) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e1424
             grind)
          | exact superpose b3e1424 b3e21
          | exact resolve b3e21 b3e1424
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1596 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e1538
             grind)
          | exact superpose b3e1538 b3e20
          | exact resolve b3e20 b3e1538
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1538
        have b3e1622 : False := by grind
        exact b3e1622
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 X1)) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
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
          have b4e31 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (σ y)) := by
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
          have b4e33 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 (M.op X2 X3) X3
               have i₂ := b4e13 X0 X3 X2
               grind)
            | (have i₁ := b4e13 X0 (M.op X0 X0) X0
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b4e487 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X1 (M.op X1 X1)) (M.op X0 (M.op X0 X0))) := by
            intro X0 X1
            grind
          clear b4e33
          have b4e507 : ∀ X1 : G, (M.op x y) = (k (M.op X1 (M.op X1 X1)) (M.op x y)) := by
            intro X1
            first
            | (have i₁ := b4e487 x X1
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e487
            | exact resolve b4e487 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e487
          have b4e555 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
            first
            | (have i₁ := b4e507 x
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e507
            | exact resolve b4e507 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e507
          have b4e796 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e57 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57
          have b4e797 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e796 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e796
          have b4e1131 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e797 (M.op x y)
               have i₂ := b4e555
               grind)
            | exact superpose b4e555 b4e797
            | (have j0 := b4e797 (M.op x y)
               grind)
            | exact resolve b4e797 b4e555
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e555 b4e797
          have b4e1137 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
          clear b4e1131
          have b4e1203 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e31 (σ (M.op x y))
               have i₂ := b4e1137
               grind)
            | exact superpose b4e1137 b4e31
            | exact resolve b4e31 b4e1137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e1226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e1203
               have i₂ := b4e1137
               grind)
            | exact superpose b4e1137 b4e1203
            | exact resolve b4e1203 b4e1137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1137 b4e1203
          have b4e1238 : False := by grind
          exact b4e1238
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 X1)) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
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
          have b5e28 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X4 X3)) := by
            intro X0 X1 X3 X4
            first
            | (have i₁ := b5e13 x X3 X4
               have i₂ := b5e13 x X0 X1
               grind)
            | (have i₁ := b5e13 x X1 x
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
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
          have b5e32 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 (M.op X2 X3) X3
               have i₂ := b5e13 X0 X3 X2
               grind)
            | (have i₁ := b5e13 X0 (M.op X0 X0) X0
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op x y) := by
            intro X1 X2
            first
            | (have i₁ := b5e13 x X1 X2
               have i₂ := b5e30 x
               grind)
            | exact superpose b5e30 b5e13
            | exact resolve b5e13 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) := by
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
          have b5e45 : y = (M.op x x) ∨ y = (k x y) := by grind
          clear b5e41
          have b5e48 : y = (k x y) := by
            first
            | (have r₁ := b5e45
               have r₂ := b5e21
               grind)
            | exact resolve b5e45 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
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
          have b5e59 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b5e373 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X1 (M.op X1 X1)) (M.op X0 (M.op X0 X0))) := by
            intro X0 X1
            grind
          clear b5e32
          have b5e391 : ∀ X1 : G, (M.op x y) = (k (M.op X1 (M.op X1 X1)) (M.op x y)) := by
            intro X1
            first
            | (have i₁ := b5e373 x X1
               have i₂ := b5e30 x
               grind)
            | exact superpose b5e30 b5e373
            | exact resolve b5e373 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e373
          have b5e434 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
            first
            | (have i₁ := b5e391 x
               have i₂ := b5e30 x
               grind)
            | exact superpose b5e30 b5e391
            | exact resolve b5e391 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e391
          have b5e521 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e59 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e522 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e521
               have r₂ := b5e24
               grind)
            | exact resolve b5e521 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e521
          have b5e523 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e522
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e522
            | exact resolve b5e522 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e522
          have b5e524 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e523
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e523
            | exact resolve b5e523 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e523
          have b5e525 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e524
               grind)
            | exact superpose b5e524 b5e20
            | exact resolve b5e20 b5e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e532 : (M.op x y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e37 (σ y) (σ x)
               have i₂ := b5e524
               grind)
            | exact superpose b5e524 b5e37
            | exact resolve b5e37 b5e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e620 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X1) (σ X0)
               have i₂ := b5e52 X1 X0
               grind)
            | exact superpose b5e52 b5e17
            | (have j0 := b5e17 (σ X1) (σ X0)
               have j1 := b5e52 X1 X0
               grind)
            | (have r₁ := b5e17 (σ X1) (σ X1)
               have r₂ := b5e52 X1 X1
               grind)
            | (have r₁ := b5e17 (σ X0) (σ X1)
               have r₂ := b5e52 X0 X1
               grind)
            | exact resolve b5e17 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e627 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e52 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e628 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e627 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e627
          have b5e630 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e620 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e620
          have b5e631 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e630 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e630
          have b5e652 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e631 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e631
            | (have j0 := b5e631 X0 X1
               grind)
            | exact resolve b5e631 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e631
          have b5e706 : (M.op x y) = (σ (k y y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) := by
            first
            | (have i₁ := b5e52 y y
               have i₂ := b5e532
               grind)
            | exact superpose b5e532 b5e52
            | exact resolve b5e52 b5e532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52 b5e532
          have b5e721 : (M.op x y) = (σ (k y y)) ∨ (M.op x y) = (σ y) := by grind
          clear b5e706
          have b5e954 : (k y y) = (τ (M.op x y)) ∨ (M.op x y) = (σ y) := by
            first
            | (have i₁ := b5e14 (k y y)
               have i₂ := b5e721
               grind)
            | exact superpose b5e721 b5e14
            | exact resolve b5e14 b5e721
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e721
          have b5e1120 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            first
            | (have i₁ := b5e628 (M.op x y)
               have i₂ := b5e434
               grind)
            | exact superpose b5e434 b5e628
            | (have j0 := b5e628 (M.op x y)
               grind)
            | exact resolve b5e628 b5e434
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e434 b5e628
          have b5e1127 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
          clear b5e1120
          have b5e1207 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            intro X0 X1
            first
            | (have i₁ := b5e28 X0 X1 (σ (M.op x y)) (σ (M.op x y))
               have i₂ := b5e1127
               grind)
            | exact superpose b5e1127 b5e28
            | exact resolve b5e28 b5e1127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e1215 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e1207 X0 X1
               have i₂ := b5e1127
               grind)
            | exact superpose b5e1127 b5e1207
            | exact resolve b5e1207 b5e1127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1127 b5e1207
          have b5e1226 : (M.op x y) = (σ (M.op x y)) := by
            first
            | (have i₁ := b5e1215 x x
               have i₂ := b5e37 x x
               grind)
            | exact superpose b5e37 b5e1215
            | exact resolve b5e1215 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1215
          have b5e1282 : (M.op x y) ≠ (σ y) := by
            first
            | (have i₁ := b5e525
               have i₂ := b5e1226
               grind)
            | exact superpose b5e1226 b5e525
            | exact resolve b5e525 b5e1226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e525
          have b5e1283 : (M.op x y) = (τ (M.op x y)) := by
            first
            | (have i₁ := b5e14 (M.op x y)
               have i₂ := b5e1226
               grind)
            | exact superpose b5e1226 b5e14
            | exact resolve b5e14 b5e1226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1226
          have b5e1375 : (M.op x y) = (k y y) ∨ (M.op x y) = (σ y) := by
            first
            | (have i₁ := b5e954
               have i₂ := b5e1283
               grind)
            | exact superpose b5e1283 b5e954
            | exact resolve b5e954 b5e1283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e954 b5e1283
          have b5e1384 : (M.op x y) = (k y y) := by
            first
            | (have r₁ := b5e1375
               have r₂ := b5e1282
               grind)
            | exact resolve b5e1375 b5e1282
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1282 b5e1375
          have b5e1477 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e18 y y
               have i₂ := b5e1384
               grind)
            | exact superpose b5e1384 b5e18
            | (have j0 := b5e18 y y
               grind)
            | exact resolve b5e18 b5e1384
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1384
          have b5e1478 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by grind
          clear b5e1477
          have b5e3102 : ∀ X0 X1 : G, (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
            intro X0 X1
            grind
          clear b5e652
          have b5e3144 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e3102 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e3102
            | (have j0 := b5e3102 X0 X1
               grind)
            | exact resolve b5e3102 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3102
          have b5e3145 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e3144 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3144
          have b5e17990 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e3145 x y
               grind)
            | exact superpose b5e3145 b5e24
            | (have j1 := b5e3145 x y
               grind)
            | exact resolve b5e24 b5e3145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3145
          have b5e18259 : (σ y) ≠ (σ (M.op y x)) ∨ (σ x) = (σ (M.op y x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e17990
               have i₂ := b5e18 y x
               grind)
            | exact superpose b5e18 b5e17990
            | (have j1 := b5e18 y x
               grind)
            | exact resolve b5e17990 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17990
          have b5e18273 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e18259
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e18259
            | exact resolve b5e18259 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e18259
          have b5e18274 : (σ x) = (σ (M.op y x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
          clear b5e18273
          have b5e18279 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e18274
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e18274
            | exact resolve b5e18274 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e18274
          have b5e25730 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e1478
               have i₂ := b5e18279
               grind)
            | exact superpose b5e18279 b5e1478
            | exact resolve b5e1478 b5e18279
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1478 b5e18279
          have b5e25762 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
          clear b5e25730
          have b5e26425 : x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e37 y x
               have i₂ := b5e25762
               grind)
            | exact superpose b5e25762 b5e37
            | exact resolve b5e37 b5e25762
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e25762
          have b5e26440 : x = y ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e26425
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e26425
            | exact resolve b5e26425 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26425
          have b5e26441 : (σ x) = (σ y) ∨ x = y := by grind
          clear b5e26440
          have b5e26997 : y = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e14 y
               have i₂ := b5e26441
               grind)
            | exact superpose b5e26441 b5e14
            | exact resolve b5e14 b5e26441
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26441
          have b5e27133 : x = y ∨ x = y := by
            first
            | (have i₁ := b5e26997
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e26997
            | exact resolve b5e26997 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26997
          have b5e27134 : x = y := by grind
          clear b5e27133
          have b5e27823 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e27134
               grind)
            | exact superpose b5e27134 b5e24
            | exact resolve b5e24 b5e27134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e27833 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e524
               have i₂ := b5e27134
               grind)
            | exact superpose b5e27134 b5e524
            | exact resolve b5e524 b5e27134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e524 b5e27134
          have b5e27901 : False := by grind
          exact b5e27901
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 X1)) := by
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
        have b6e39 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (σ x) X0 X1
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e40 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X4 X3)) := by
          intro X0 X1 X3 X4
          first
          | (have i₁ := b6e12 x X3 X4
             have i₂ := b6e12 x X0 X1
             grind)
          | (have i₁ := b6e12 x X1 x
             have i₂ := b6e12 X0 x x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e43 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X2)) = (M.op (M.op X3 X3) (M.op X0 (M.op X1 X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X2 (M.op X3 X3) X3
             have i₂ := b6e12 X3 X0 X1
             grind)
          | (have i₁ := b6e12 X0 (M.op X2 X1) X1
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e76 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
        have b6e77 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
        have b6e78 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op X3 X2)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X1 X2 X3
             have i₂ := b6e17 X1 X0
             grind)
          | (have i₁ := b6e12 X0 X1 X2
             have i₂ := b6e17 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e17 b6e12
          | (have j1 := b6e17 X1 X0
             grind)
          | exact resolve b6e12 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e83 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e77
             have r₂ := b6e20
             grind)
          | exact resolve b6e77 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e84 : y = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e76
             have r₂ := b6e20
             grind)
          | exact resolve b6e76 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e76
        have b6e86 : (σ (M.op x y)) = (σ y) := by
          first
          | (have r₁ := b6e83
             have r₂ := b6e21
             grind)
          | exact resolve b6e83 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e87 : y = (M.op x y) := by
          first
          | (have r₁ := b6e84
             have r₂ := b6e21
             grind)
          | exact resolve b6e84 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84
        have b6e99 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e19
             have i₂ := b6e39 X0 X1
             grind)
          | exact superpose b6e39 b6e19
          | exact resolve b6e19 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e109 : ∀ X0 X1 : G, (σ y) ≠ (M.op X0 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e99 X0 X1
             have i₂ := b6e86
             grind)
          | exact superpose b6e86 b6e99
          | exact resolve b6e99 b6e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86 b6e99
        have b6e141 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y y) := by
          intro X0 X1
          first
          | (have i₁ := b6e40 X0 X1 y x
             have i₂ := b6e87
             grind)
          | exact superpose b6e87 b6e40
          | exact resolve b6e40 b6e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e156 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (M.op X2 X3) (M.op X0 (M.op X1 X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e39 (M.op X2 X3) X3
             have i₂ := b6e40 X3 X2 X0 X1
             grind)
          | (have i₁ := b6e39 (M.op X2 X3) X3
             have i₂ := b6e40 X0 X1 X3 X2
             grind)
          | exact superpose b6e40 b6e39
          | exact resolve b6e39 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e187 : (σ y) ≠ (M.op y y) := by
          first
          | (have i₁ := b6e109 y x
             have i₂ := b6e87
             grind)
          | exact superpose b6e87 b6e109
          | exact resolve b6e109 b6e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87
        have b6e276 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X1))) = (M.op X4 (M.op X5 X4)) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b6e40 x x X4 X5
             have i₂ := b6e43 X1 X2 x X0
             grind)
          | exact superpose b6e43 b6e40
          | exact resolve b6e40 b6e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e43
        have b6e306 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op (M.op X0 X0) (M.op X1 (M.op X2 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e276 X0 X1 X2 x x
             have i₂ := b6e141 x x
             grind)
          | exact superpose b6e141 b6e276
          | exact resolve b6e276 b6e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e141 b6e276
        have b6e338 : (M.op (σ x) (σ y)) = (M.op y y) := by
          first
          | (have i₁ := b6e306 x x x
             have i₂ := b6e156 x x x x
             grind)
          | exact superpose b6e156 b6e306
          | exact resolve b6e306 b6e156
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e156 b6e306
        have b6e595 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X1 X0)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
          intro X0 X1
          first
          | (have i₁ := b6e78 (σ x) (σ x) x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e78
          | exact resolve b6e78 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78
        have b6e753 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e595 x x
             have r₂ := b6e109 x x
             grind)
          | exact resolve b6e595 b6e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e109 b6e595
        have b6e771 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e753
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e753
          | exact resolve b6e753 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e753
        have b6e1645 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e771
             grind)
          | exact superpose b6e771 b6e13
          | exact resolve b6e13 b6e771
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1660 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1645
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1645
          | exact resolve b6e1645 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1645
        have b6e1765 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e1660
             grind)
          | exact superpose b6e1660 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e1660
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1660
        have b6e1766 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e1765
        have b6e1768 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e1766
             have r₂ := b6e20
             grind)
          | exact resolve b6e1766 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1766
        have b6e1870 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e1768
        have b6e2060 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e771
             have i₂ := b6e1870
             grind)
          | exact superpose b6e1870 b6e771
          | exact resolve b6e771 b6e1870
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e771 b6e1870
        have b6e2067 : (σ x) = (σ y) := by grind
        clear b6e2060
        have b6e2139 : (M.op (σ x) (σ x)) = (M.op y y) := by
          first
          | (have i₁ := b6e338
             have i₂ := b6e2067
             grind)
          | exact superpose b6e2067 b6e338
          | exact resolve b6e338 b6e2067
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e338 b6e2067
        have b6e2164 : (σ y) = (M.op y y) := by
          first
          | (have i₁ := b6e2139
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e2139
          | exact resolve b6e2139 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2139
        have b6e2175 : False := by grind
        exact b6e2175
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 X1)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
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
          have b7e28 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X4 X3)) := by
            intro X0 X1 X3 X4
            first
            | (have i₁ := b7e13 x X3 X4
               have i₂ := b7e13 x X0 X1
               grind)
            | (have i₁ := b7e13 x X1 x
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (σ y)) := by
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
          have b7e40 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e43 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e40
          have b7e44 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e43
               have r₂ := b7e23
               grind)
            | exact resolve b7e43 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e45 : (σ y) = (σ (k x y)) := by
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
          have b7e48 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e14
            | exact resolve b7e14 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e49 : y = (k x y) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e48
            | exact resolve b7e48 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e56 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e45
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e45
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e45 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e57 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op X3 X2)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X1 X2 X3
               have i₂ := b7e18 X1 X0
               grind)
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e18 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X1 X0
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e58 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e62 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e56
               have r₂ := b7e21
               grind)
            | exact resolve b7e56 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e63 : (σ (M.op x y)) = (σ y) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e22
               grind)
            | exact resolve b7e62 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e65 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
          have b7e66 : y = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e21
               grind)
            | exact resolve b7e65 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e68 : y = (M.op x y) := by
            first
            | (have r₁ := b7e66
               have r₂ := b7e22
               grind)
            | exact resolve b7e66 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e80 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 y x
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e13
            | exact resolve b7e13 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e92 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e28 X0 X1 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e28
            | exact resolve b7e28 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e98 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y y) := by
            intro X0 X1
            first
            | (have i₁ := b7e28 X0 X1 y x
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e28
            | exact resolve b7e28 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e117 : (M.op (σ x) (σ y)) = (M.op y y) := by
            first
            | (have i₁ := b7e92 x x
               have i₂ := b7e98 x x
               grind)
            | exact superpose b7e98 b7e92
            | exact resolve b7e92 b7e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e153 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (σ (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b7e20
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e20
            | exact resolve b7e20 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e157 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ y) (M.op X0 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 (σ y) (σ x)
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e13
            | exact resolve b7e13 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e158 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ y) (M.op y y)) := by
            intro X1
            first
            | (have i₁ := b7e157 x X1
               have i₂ := b7e80 x
               grind)
            | exact superpose b7e80 b7e157
            | exact resolve b7e157 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e157
          have b7e162 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (σ y) := by
            intro X0
            first
            | (have i₁ := b7e153 X0
               have i₂ := b7e63
               grind)
            | exact superpose b7e63 b7e153
            | exact resolve b7e153 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63 b7e153
          have b7e174 : (M.op y y) = (M.op (σ y) (M.op y y)) := by
            first
            | (have i₁ := b7e158 x
               have i₂ := b7e80 x
               grind)
            | exact superpose b7e80 b7e158
            | exact resolve b7e158 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e158
          have b7e178 : (σ y) ≠ (M.op y y) := by
            first
            | (have i₁ := b7e162 x
               have i₂ := b7e80 x
               grind)
            | exact superpose b7e80 b7e162
            | exact resolve b7e162 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80 b7e162
          have b7e620 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X1 X0)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e57 (σ x) (σ y) x x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e57
            | (have j0 := b7e57 (σ x) (σ y) x x
               grind)
            | exact resolve b7e57 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e771 : (σ y) = (M.op y y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e620 x x
               have i₂ := b7e98 x x
               grind)
            | exact superpose b7e98 b7e620
            | exact resolve b7e620 b7e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98 b7e620
          have b7e804 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b7e771
               have r₂ := b7e178
               grind)
            | exact resolve b7e771 b7e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e771
          have b7e812 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e804
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e804
            | exact resolve b7e804 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e804
          have b7e814 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b7e812
               have i₂ := b7e117
               grind)
            | exact superpose b7e117 b7e812
            | exact resolve b7e812 b7e117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e117 b7e812
          have b7e1496 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e814
               grind)
            | exact superpose b7e814 b7e14
            | exact resolve b7e14 b7e814
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e814
          have b7e1510 : y = (k y x) ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b7e1496
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e1496
            | exact resolve b7e1496 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1496
          have b7e1560 : y = (M.op y x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b7e58 x y
               have i₂ := b7e1510
               grind)
            | exact superpose b7e1510 b7e58
            | (have j0 := b7e58 y x
               grind)
            | exact resolve b7e58 b7e1510
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58 b7e1510
          have b7e1563 : x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op y y) := by
            first
            | (have r₁ := b7e1560
               have r₂ := b7e22
               grind)
            | exact resolve b7e1560 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1560
          have b7e1571 : x = y ∨ x = y ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b7e1563
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e1563
            | exact resolve b7e1563 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1563
          have b7e1572 : (σ x) = (M.op y y) ∨ x = y := by grind
          clear b7e1571
          have b7e1634 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b7e174
               have i₂ := b7e1572
               grind)
            | exact superpose b7e1572 b7e174
            | exact resolve b7e174 b7e1572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e174
          have b7e1635 : (σ x) ≠ (σ y) ∨ x = y := by
            first
            | (have i₁ := b7e178
               have i₂ := b7e1572
               grind)
            | exact superpose b7e1572 b7e178
            | exact resolve b7e178 b7e1572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e178 b7e1572
          have b7e1661 : (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b7e1634
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e1634
            | exact resolve b7e1634 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1634
          have b7e1665 : x = y := by
            first
            | (have r₁ := b7e1661
               have r₂ := b7e1635
               grind)
            | exact resolve b7e1661 b7e1635
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1635 b7e1661
          have b7e1740 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e1665
               grind)
            | exact superpose b7e1665 b7e22
            | exact resolve b7e22 b7e1665
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1747 : x = (M.op x x) := by
            first
            | (have i₁ := b7e68
               have i₂ := b7e1665
               grind)
            | exact superpose b7e1665 b7e68
            | exact resolve b7e68 b7e1665
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68 b7e1665
          have b7e1756 : False := by grind
          exact b7e1756
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
          have b8e58 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b8e269 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e58 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e270 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e269
               have r₂ := b8e24
               grind)
            | exact resolve b8e269 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e269
          have b8e271 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e270
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e270
            | exact resolve b8e270 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e270
          have b8e272 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e271
               grind)
            | exact superpose b8e271 b8e20
            | exact resolve b8e20 b8e271
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e271
          have b8e384 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e272
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e272
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e272 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e272
          have b8e385 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e384
          have b8e387 : y = (M.op y x) := by
            first
            | (have r₁ := b8e385
               have r₂ := b8e21
               grind)
            | exact resolve b8e385 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e385
          have b8e389 : False := by grind
          exact b8e389

/-- `Equation4301`: `x ◇ (x ◇ y) = z ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pxx_y_pxy_Equation4301 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4301 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4301.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = b :=
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
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x y) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e22
        | exact resolve b0e22 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e24 : False := by grind
      exact b0e24
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e31 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 x y X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ x) (σ x) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e12 X1 x X3
             have i₂ := b1e12 X1 x X0
             grind)
          | (have i₁ := b1e12 X0 X0 x
             have i₂ := b1e12 X0 X1 X0
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X0 : G, y = (M.op X0 (M.op x X0)) := by
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
        have b1e43 : y = (M.op y y) := by
          first
          | (have i₁ := b1e42 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e42
          | exact resolve b1e42 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e44 : ∀ X0 X1 : G, y = (M.op (M.op x X1) (M.op X0 (M.op x X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e42 (M.op x X1)
             have i₂ := b1e12 x X1 X0
             grind)
          | (have i₁ := b1e42 (M.op X0 x)
             have i₂ := b1e12 X0 X1 x
             grind)
          | exact superpose b1e12 b1e42
          | exact resolve b1e42 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 (M.op x X0) X1
             have i₂ := b1e42 X0
             grind)
          | exact superpose b1e42 b1e12
          | exact resolve b1e12 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e53 : ∀ X1 : G, y = (M.op (M.op x X1) y) := by
          intro X1
          first
          | (have i₁ := b1e44 x X1
             have i₂ := b1e42 x
             grind)
          | exact superpose b1e42 b1e44
          | exact resolve b1e44 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e62 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b1e15 y y
             have i₂ := b1e43
             grind)
          | exact superpose b1e43 b1e15
          | (have r₁ := b1e15 y y
             have r₂ := b1e43
             grind)
          | exact resolve b1e15 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e65 : y = (k y y) := by grind
        clear b1e62
        have b1e70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b1e123 : ∀ X0 X1 : G, (M.op (M.op x X0) y) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e35 (M.op x X0) X0 X1
             have i₂ := b1e42 X0
             grind)
          | exact superpose b1e42 b1e35
          | exact resolve b1e35 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e139 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op x X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b1e35 X0 X1 (M.op x X1)
             have i₂ := b1e42 X1
             grind)
          | exact superpose b1e42 b1e35
          | exact resolve b1e35 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35 b1e42
        have b1e176 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e139 X0 X1
             have i₂ := b1e53 X1
             grind)
          | exact superpose b1e53 b1e139
          | exact resolve b1e139 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e139
        have b1e184 : ∀ X0 : G, (M.op (M.op x X0) y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e123 X0 x
             have i₂ := b1e52 X0 x
             grind)
          | exact superpose b1e52 b1e123
          | exact resolve b1e123 b1e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52 b1e123
        have b1e196 : ∀ X0 : G, y = (M.op X0 y) := by
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
        have b1e215 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 y
             have i₂ := b1e196 X0
             grind)
          | exact superpose b1e196 b1e15
          | (have j0 := b1e15 X0 y
             grind)
          | (have r₁ := b1e15 X0 y
             have r₂ := b1e196 X0
             grind)
          | exact resolve b1e15 b1e196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e219 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e215 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e215
        have b1e389 : (M.op (σ x) (σ y)) = (M.op y y) := by
          first
          | (have i₁ := b1e32 y
             have i₂ := b1e196 (σ x)
             grind)
          | exact superpose b1e196 b1e32
          | exact resolve b1e32 b1e196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e417 : y = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e389
             have i₂ := b1e196 y
             grind)
          | exact superpose b1e196 b1e389
          | exact resolve b1e389 b1e196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e196 b1e389
        have b1e1150 : ∀ X0 : G, y = (M.op X0 (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e176 X0 X0
             have i₂ := b1e219 X0
             grind)
          | exact superpose b1e219 b1e176
          | exact resolve b1e176 b1e219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e176
        have b1e2012 : y ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e417
             grind)
          | exact superpose b1e417 b1e21
          | exact resolve b1e21 b1e417
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e417
        have b1e3910 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e70 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70
        have b1e3912 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e3910 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3910
        have b1e3924 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k (σ X0) y) := by
          intro X0
          first
          | (have i₁ := b1e3912 X0
             have i₂ := b1e219 (σ X0)
             grind)
          | exact superpose b1e219 b1e3912
          | (have j0 := b1e3912 X0
             grind)
          | exact resolve b1e3912 b1e219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3912
        have b1e6754 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b1e3924 y
             have i₂ := b1e65
             grind)
          | exact superpose b1e65 b1e3924
          | (have j0 := b1e3924 y
             grind)
          | exact resolve b1e3924 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65 b1e3924
        have b1e6761 : (σ y) = (k (σ y) y) := by grind
        clear b1e6754
        have b1e6789 : y = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e1150 (σ y)
             have i₂ := b1e6761
             grind)
          | exact superpose b1e6761 b1e1150
          | exact resolve b1e1150 b1e6761
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1150
        have b1e6793 : y = (k (σ y) y) := by
          first
          | (have i₁ := b1e6789
             have i₂ := b1e219 (σ y)
             grind)
          | exact superpose b1e219 b1e6789
          | exact resolve b1e6789 b1e219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e219 b1e6789
        have b1e6871 : y = (σ y) := by
          first
          | (have i₁ := b1e6761
             have i₂ := b1e6793
             grind)
          | exact superpose b1e6793 b1e6761
          | exact resolve b1e6761 b1e6793
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6761 b1e6793
        have b1e6883 : False := by grind
        exact b1e6883
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e31 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b2e12 x y X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e12 X1 x X3
             have i₂ := b2e12 X1 x X0
             grind)
          | (have i₁ := b2e12 X0 X0 x
             have i₂ := b2e12 X0 X1 X0
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e40 : ∀ X0 : G, y = (M.op X0 (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b2e31 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e31
          | exact resolve b2e31 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e41 : y = (M.op y y) := by
          first
          | (have i₁ := b2e40 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e40
          | exact resolve b2e40 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e42 : ∀ X0 X1 : G, y = (M.op (M.op x X1) (M.op X0 (M.op x X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e40 (M.op x X1)
             have i₂ := b2e12 x X1 X0
             grind)
          | (have i₁ := b2e40 (M.op X0 x)
             have i₂ := b2e12 X0 X1 x
             grind)
          | exact superpose b2e12 b2e40
          | exact resolve b2e40 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e50 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 (M.op x X0) X1
             have i₂ := b2e40 X0
             grind)
          | exact superpose b2e40 b2e12
          | exact resolve b2e12 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e51 : ∀ X1 : G, y = (M.op (M.op x X1) y) := by
          intro X1
          first
          | (have i₁ := b2e42 x X1
             have i₂ := b2e40 x
             grind)
          | exact superpose b2e40 b2e42
          | exact resolve b2e42 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42
        have b2e58 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b2e15 y y
             have i₂ := b2e41
             grind)
          | exact superpose b2e41 b2e15
          | (have r₁ := b2e15 y y
             have r₂ := b2e41
             grind)
          | exact resolve b2e15 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e61 : y = (k y y) := by grind
        clear b2e58
        have b2e65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e99 : ∀ X0 X1 : G, (M.op (M.op x X0) y) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e34 (M.op x X0) X0 X1
             have i₂ := b2e40 X0
             grind)
          | exact superpose b2e40 b2e34
          | exact resolve b2e34 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e113 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op x X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b2e34 X0 X1 (M.op x X1)
             have i₂ := b2e40 X1
             grind)
          | exact superpose b2e40 b2e34
          | exact resolve b2e34 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e40
        have b2e148 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e113 X0 X1
             have i₂ := b2e51 X1
             grind)
          | exact superpose b2e51 b2e113
          | exact resolve b2e113 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e113
        have b2e156 : ∀ X0 : G, (M.op (M.op x X0) y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e99 X0 x
             have i₂ := b2e50 X0 x
             grind)
          | exact superpose b2e50 b2e99
          | exact resolve b2e99 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50 b2e99
        have b2e168 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e156 X0
             have i₂ := b2e51 X0
             grind)
          | exact superpose b2e51 b2e156
          | exact resolve b2e156 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e156
        have b2e187 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b2e15 X0 y
             have i₂ := b2e168 X0
             grind)
          | exact superpose b2e168 b2e15
          | (have j0 := b2e15 X0 y
             grind)
          | (have r₁ := b2e15 X0 y
             have r₂ := b2e168 X0
             grind)
          | exact resolve b2e15 b2e168
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e191 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b2e187 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e187
        have b2e2027 : ∀ X0 : G, y = (M.op X0 (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b2e148 X0 X0
             have i₂ := b2e191 X0
             grind)
          | exact superpose b2e191 b2e148
          | exact resolve b2e148 b2e191
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e148
        have b2e3355 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e65 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e3357 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e3355 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3355
        have b2e3368 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k (σ X0) y) := by
          intro X0
          first
          | (have i₁ := b2e3357 X0
             have i₂ := b2e191 (σ X0)
             grind)
          | exact superpose b2e191 b2e3357
          | (have j0 := b2e3357 X0
             grind)
          | exact resolve b2e3357 b2e191
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3357
        have b2e5819 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b2e3368 y
             have i₂ := b2e61
             grind)
          | exact superpose b2e61 b2e3368
          | (have j0 := b2e3368 y
             grind)
          | exact resolve b2e3368 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61 b2e3368
        have b2e5823 : (σ y) = (k (σ y) y) := by grind
        clear b2e5819
        have b2e5838 : y = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e2027 (σ y)
             have i₂ := b2e5823
             grind)
          | exact superpose b2e5823 b2e2027
          | exact resolve b2e2027 b2e5823
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2027
        have b2e5842 : y = (k (σ y) y) := by
          first
          | (have i₁ := b2e5838
             have i₂ := b2e191 (σ y)
             grind)
          | exact superpose b2e191 b2e5838
          | exact resolve b2e5838 b2e191
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e191 b2e5838
        have b2e5855 : y = (σ y) := by
          first
          | (have i₁ := b2e5823
             have i₂ := b2e5842
             grind)
          | exact superpose b2e5842 b2e5823
          | exact resolve b2e5823 b2e5842
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5823 b2e5842
        have b2e5918 : y ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e5855
             grind)
          | exact superpose b2e5855 b2e21
          | exact resolve b2e21 b2e5855
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5855
        have b2e5938 : False := by grind
        exact b2e5938
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x X0)) := by
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
        have b3e28 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ x) (σ y) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
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
        have b3e38 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X0 X1 x
             have i₂ := b3e12 X0 X2 x
             grind)
          | (have i₁ := b3e12 X1 X1 X1
             have i₂ := b3e12 X1 X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ x) X0)) := by
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
        have b3e40 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x X1) (M.op X0 (M.op x X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e27 (M.op x X1)
             have i₂ := b3e12 x X1 X0
             grind)
          | (have i₁ := b3e27 (M.op X0 x)
             have i₂ := b3e12 X0 X1 x
             grind)
          | exact superpose b3e12 b3e27
          | exact resolve b3e27 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e50 : ∀ X1 : G, (M.op x y) = (M.op (M.op x X1) (M.op x y)) := by
          intro X1
          first
          | (have i₁ := b3e40 x X1
             have i₂ := b3e27 x
             grind)
          | exact superpose b3e27 b3e40
          | exact resolve b3e40 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e87 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e39 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e39
          | exact resolve b3e39 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e91 : (σ y) = (M.op (M.op x (σ x)) (M.op x y)) := by
          first
          | (have i₁ := b3e39 (M.op x (σ x))
             have i₂ := b3e27 (σ x)
             grind)
          | exact superpose b3e27 b3e39
          | exact resolve b3e39 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e101 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (M.op (σ x) X0) X1
             have i₂ := b3e39 X0
             grind)
          | exact superpose b3e39 b3e12
          | exact resolve b3e12 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e102 : (M.op x y) = (σ y) := by
          first
          | (have i₁ := b3e91
             have i₂ := b3e50 (σ x)
             grind)
          | exact superpose b3e50 b3e91
          | exact resolve b3e91 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e91
        have b3e107 : y ≠ (σ y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e102
             grind)
          | exact superpose b3e102 b3e20
          | exact resolve b3e20 b3e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e169 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op x y)) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e31 (M.op x X0) X0 X1
             have i₂ := b3e27 X0
             grind)
          | exact superpose b3e27 b3e31
          | exact resolve b3e31 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e31
        have b3e243 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e169 X0 x
             have i₂ := b3e101 X0 x
             grind)
          | exact superpose b3e101 b3e169
          | exact resolve b3e169 b3e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e101 b3e169
        have b3e264 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e243 X0
             have i₂ := b3e50 X0
             grind)
          | exact superpose b3e50 b3e243
          | exact resolve b3e243 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50 b3e243
        have b3e275 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e264 X0
             have i₂ := b3e102
             grind)
          | exact superpose b3e102 b3e264
          | exact resolve b3e264 b3e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e102 b3e264
        have b3e317 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e38 X0 X1 (M.op (σ x) X0)
             have i₂ := b3e39 X0
             grind)
          | exact superpose b3e39 b3e38
          | exact resolve b3e38 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e368 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ y) := by
          intro X0 X1
          first
          | (have i₁ := b3e317 X0 X1
             have i₂ := b3e275 X0
             grind)
          | exact superpose b3e275 b3e317
          | exact resolve b3e317 b3e275
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e275 b3e317
        have b3e944 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e87
             grind)
          | exact superpose b3e87 b3e15
          | (have r₁ := b3e15 (σ y) (σ y)
             have r₂ := b3e87
             grind)
          | exact resolve b3e15 b3e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e87
        have b3e952 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b3e944
        have b3e956 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e952
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e952
          | exact resolve b3e952 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e952
        have b3e1084 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e956
             grind)
          | exact superpose b3e956 b3e13
          | exact resolve b3e13 b3e956
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e956
        have b3e1086 : y = (k y y) := by
          first
          | (have i₁ := b3e1084
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e1084
          | exact resolve b3e1084 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1084
        have b3e1632 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e1086
             grind)
          | exact superpose b3e1086 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e1086
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1086
        have b3e1633 : y = (M.op y y) := by grind
        clear b3e1632
        have b3e2105 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b3e38 y X0 y
             have i₂ := b3e1633
             grind)
          | exact superpose b3e1633 b3e38
          | exact resolve b3e38 b3e1633
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e2107 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b3e2105 X0
             have i₂ := b3e1633
             grind)
          | exact superpose b3e1633 b3e2105
          | exact resolve b3e2105 b3e1633
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1633 b3e2105
        have b3e2117 : y = (σ y) := by
          first
          | (have i₁ := b3e2107 x
             have i₂ := b3e368 y x
             grind)
          | exact superpose b3e368 b3e2107
          | exact resolve b3e2107 b3e368
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e368 b3e2107
        have b3e2126 : False := by grind
        exact b3e2126
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
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
          have b4e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b4e138 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op x X1) (M.op x y)) := by
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
          have b4e164 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e138 X0 X1
               have i₂ := b4e54 X1
               grind)
            | exact superpose b4e54 b4e138
            | exact resolve b4e138 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54 b4e138
          have b4e169 : (M.op x y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e164 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e164
            | exact resolve b4e164 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e186 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 x
               have i₂ := b4e164 x X0
               grind)
            | exact superpose b4e164 b4e13
            | exact resolve b4e13 b4e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e164
          have b4e229 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op x y)) := by
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
          have b4e282 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b4e229 X0 x
               have i₂ := b4e186 X0 x
               grind)
            | exact superpose b4e186 b4e229
            | exact resolve b4e229 b4e186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e229
          have b4e325 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (k X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b4e16 X0 (M.op x y)
               have i₂ := b4e282 X0
               grind)
            | exact superpose b4e282 b4e16
            | (have j0 := b4e16 X0 (M.op x y)
               grind)
            | (have r₁ := b4e16 X0 (M.op x y)
               have r₂ := b4e282 X0
               grind)
            | exact resolve b4e16 b4e282
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e333 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) := by
            intro X0
            first
            | (have j0 := b4e325 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e325
          have b4e405 : (M.op x y) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e169
               grind)
            | exact superpose b4e169 b4e20
            | exact resolve b4e20 b4e169
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e169
          have b4e1132 : ∀ X0 : G, (M.op x y) = (M.op X0 (k X0 (M.op x y))) := by
            intro X0
            first
            | (have i₁ := b4e186 X0 X0
               have i₂ := b4e333 X0
               grind)
            | exact superpose b4e333 b4e186
            | exact resolve b4e186 b4e333
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e186
          have b4e1137 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op x y))) := by
            intro X0
            first
            | (have i₁ := b4e26 X0 (M.op x y)
               have i₂ := b4e333 (τ X0)
               grind)
            | exact superpose b4e333 b4e26
            | exact resolve b4e26 b4e333
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e4517 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e64 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64
          have b4e4519 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e4517 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4517
          have b4e7452 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e1137 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e1137
            | exact resolve b4e1137 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1137
          have b4e7500 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 (M.op x y))) := by
            intro X0
            first
            | (have i₁ := b4e7452 X0
               have i₂ := b4e19 X0 (M.op x y)
               grind)
            | exact superpose b4e19 b4e7452
            | exact resolve b4e7452 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7452
          have b4e12896 : (σ (M.op x y)) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e4519 (M.op x y)
               have i₂ := b4e7500 (M.op x y)
               grind)
            | exact superpose b4e7500 b4e4519
            | (have j0 := b4e4519 (M.op x y)
               grind)
            | exact resolve b4e4519 b4e7500
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4519 b4e7500
          have b4e12905 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e12896
               have i₂ := b4e282 (M.op x y)
               grind)
            | exact superpose b4e282 b4e12896
            | exact resolve b4e12896 b4e282
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e282 b4e12896
          have b4e12906 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
          clear b4e12905
          have b4e12916 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) := by
            first
            | (have i₁ := b4e12906
               have i₂ := b4e333 (σ (M.op x y))
               grind)
            | exact superpose b4e333 b4e12906
            | exact resolve b4e12906 b4e333
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12906
          have b4e13060 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e1132 (σ (M.op x y))
               have i₂ := b4e12916
               grind)
            | exact superpose b4e12916 b4e1132
            | exact resolve b4e1132 b4e12916
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1132
          have b4e13065 : (M.op x y) = (k (σ (M.op x y)) (M.op x y)) := by
            first
            | (have i₁ := b4e13060
               have i₂ := b4e333 (σ (M.op x y))
               grind)
            | exact superpose b4e333 b4e13060
            | exact resolve b4e13060 b4e333
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e333 b4e13060
          have b4e13224 : (M.op x y) = (σ (M.op x y)) := by
            first
            | (have i₁ := b4e12916
               have i₂ := b4e13065
               grind)
            | exact superpose b4e13065 b4e12916
            | exact resolve b4e12916 b4e13065
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12916 b4e13065
          have b4e13242 : False := by grind
          exact b4e13242
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x y) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e61 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ x) X0
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 (σ x) X0
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e80 : y = (k x y) ∨ y = (M.op x y) := by grind
          have b5e85 : y = (k x y) := by
            first
            | (have r₁ := b5e80
               have r₂ := b5e21
               grind)
            | exact resolve b5e80 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e80
          have b5e2704 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e61 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e2705 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e2704
               have r₂ := b5e23
               grind)
            | exact resolve b5e2704 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2704
          have b5e2706 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e2705
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e2705
            | exact resolve b5e2705 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2705
          have b5e2707 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e2706
               have i₂ := b5e85
               grind)
            | exact superpose b5e85 b5e2706
            | exact resolve b5e2706 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85 b5e2706
          have b5e2708 : False := by grind
          exact b5e2708
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e27 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) (σ y) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e30 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X1 X3)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b6e12 X1 x X3
             have i₂ := b6e12 X1 x X0
             grind)
          | (have i₁ := b6e12 X0 X0 x
             have i₂ := b6e12 X0 X1 X0
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e36 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X0 X1 x
             have i₂ := b6e12 X0 X2 x
             grind)
          | (have i₁ := b6e12 X1 X1 X1
             have i₂ := b6e12 X1 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e37 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b6e27 X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e27
          | exact resolve b6e27 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e38 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e37 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e37
          | exact resolve b6e37 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e39 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) X1) (M.op X0 (M.op (σ x) X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e37 (M.op (σ x) X1)
             have i₂ := b6e12 (σ x) X1 X0
             grind)
          | (have i₁ := b6e37 (M.op X0 (σ x))
             have i₂ := b6e12 X0 X1 (σ x)
             grind)
          | exact superpose b6e12 b6e37
          | exact resolve b6e37 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e47 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 (M.op (σ x) X0) X1
             have i₂ := b6e37 X0
             grind)
          | exact superpose b6e37 b6e12
          | exact resolve b6e12 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e48 : ∀ X1 : G, (σ y) = (M.op (M.op (σ x) X1) (σ y)) := by
          intro X1
          first
          | (have i₁ := b6e39 x X1
             have i₂ := b6e37 x
             grind)
          | exact superpose b6e37 b6e39
          | exact resolve b6e39 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e56 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e38
             grind)
          | exact superpose b6e38 b6e15
          | (have r₁ := b6e15 (σ y) (σ y)
             have r₂ := b6e38
             grind)
          | exact resolve b6e15 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e59 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b6e56
        have b6e61 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e59
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e59
          | exact resolve b6e59 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e75 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e61
             grind)
          | exact superpose b6e61 b6e13
          | exact resolve b6e13 b6e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e77 : y = (k y y) := by
          first
          | (have i₁ := b6e75
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e75
          | exact resolve b6e75 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e84 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e77
             grind)
          | exact superpose b6e77 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e85 : y = (M.op y y) := by grind
        clear b6e84
        have b6e96 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b6e12 y y X0
             have i₂ := b6e85
             grind)
          | exact superpose b6e85 b6e12
          | exact resolve b6e12 b6e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e99 : (M.op y y) = (M.op y (σ y)) := by
          first
          | (have i₁ := b6e96 x
             have i₂ := b6e47 y x
             grind)
          | exact superpose b6e47 b6e96
          | exact resolve b6e96 b6e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e96
        have b6e101 : y = (M.op y (σ y)) := by
          first
          | (have i₁ := b6e99
             have i₂ := b6e85
             grind)
          | exact superpose b6e85 b6e99
          | exact resolve b6e99 b6e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e85 b6e99
        have b6e145 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (σ y)) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e30 (M.op (σ x) X0) X0 X1
             have i₂ := b6e37 X0
             grind)
          | exact superpose b6e37 b6e30
          | exact resolve b6e30 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30 b6e37
        have b6e207 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e145 X0 x
             have i₂ := b6e47 X0 x
             grind)
          | exact superpose b6e47 b6e145
          | exact resolve b6e145 b6e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47 b6e145
        have b6e225 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e207 X0
             have i₂ := b6e48 X0
             grind)
          | exact superpose b6e48 b6e207
          | exact resolve b6e207 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48 b6e207
        have b6e249 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 (σ y)
             have i₂ := b6e225 X0
             grind)
          | exact superpose b6e225 b6e12
          | exact resolve b6e12 b6e225
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e252 : y = (σ y) := by
          first
          | (have i₁ := b6e101
             have i₂ := b6e225 y
             grind)
          | exact superpose b6e225 b6e101
          | exact resolve b6e101 b6e225
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e101 b6e225
        have b6e254 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ y) := by
          intro X0 X1
          first
          | (have i₁ := b6e249 X0 X1
             have i₂ := b6e38
             grind)
          | exact superpose b6e38 b6e249
          | exact resolve b6e249 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38 b6e249
        have b6e258 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y := by
          intro X0 X1
          first
          | (have i₁ := b6e254 X0 X1
             have i₂ := b6e252
             grind)
          | exact superpose b6e252 b6e254
          | exact resolve b6e254 b6e252
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e252 b6e254
        have b6e290 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e36 X2 X3 (M.op X0 X2)
             have i₂ := b6e12 X0 X1 X2
             grind)
          | (have i₁ := b6e36 X0 X1 (M.op X0 X1)
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e36
          | exact resolve b6e36 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e339 : ∀ X0 X1 X2 : G, y = (M.op X2 (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e290 X0 X1 X2 x
             have i₂ := b6e258 X2 x
             grind)
          | exact superpose b6e258 b6e290
          | exact resolve b6e290 b6e258
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e290
        have b6e367 : ∀ X2 : G, y = (M.op X2 y) := by
          intro X2
          first
          | (have i₁ := b6e339 x x X2
             have i₂ := b6e258 x x
             grind)
          | exact superpose b6e258 b6e339
          | exact resolve b6e339 b6e258
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e258 b6e339
        have b6e945 : y ≠ y := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e367 x
             grind)
          | exact superpose b6e367 b6e20
          | (have r₁ := b6e20
             have r₂ := b6e367 x
             grind)
          | exact resolve b6e20 b6e367
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e367
        have b6e946 : False := by grind
        exact b6e946
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x y) := by grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e86 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          have b7e91 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e86
               have r₂ := b7e23
               grind)
            | exact resolve b7e86 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e92 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e91
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e91
            | exact resolve b7e91 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e98 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e92
               grind)
            | exact superpose b7e92 b7e14
            | exact resolve b7e14 b7e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
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
          have b7e137 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
          have b7e138 : y = (M.op x y) ∨ y = (M.op x x) := by grind
          clear b7e137
          have b7e140 : y = (M.op x x) := by
            first
            | (have r₁ := b7e138
               have r₂ := b7e21
               grind)
            | exact resolve b7e138 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e138
          have b7e142 : False := by grind
          exact b7e142
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x y) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1422 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e64 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e1423 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1422
               have r₂ := b8e23
               grind)
            | exact resolve b8e1422 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1422
          have b8e1424 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1423
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1423
            | exact resolve b8e1423 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1423
          have b8e1425 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1424
               grind)
            | exact superpose b8e1424 b8e20
            | exact resolve b8e20 b8e1424
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1424
          have b8e1915 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e1425
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1425
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1425 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1425
          have b8e1916 : y = (M.op x x) ∨ y = (M.op x y) := by grind
          clear b8e1915
          have b8e1918 : y = (M.op x y) := by
            first
            | (have r₁ := b8e1916
               have r₂ := b8e22
               grind)
            | exact resolve b8e1916 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1916
          have b8e1920 : False := by grind
          exact b8e1920

/-- `Equation4325`: `x ◇ (y ◇ x) = y ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pxx_pyy_pxy_Equation4325 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4325 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4325.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op y y) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
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
      have b0e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e49 (σ X0)
           grind)
        | exact superpose b0e49 b0e17
        | exact resolve b0e17 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e55 X0
           have i₂ := b0e49 X0
           grind)
        | exact superpose b0e49 b0e55
        | exact resolve b0e55 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49 b0e55
      have b0e379 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e60 y
           grind)
        | exact superpose b0e60 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e60 y
           grind)
        | exact resolve b0e22 b0e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e60
      have b0e395 : False := by grind
      exact b0e395
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op y y) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e19
          | exact resolve b1e19 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : (M.op y y) ≠ (M.op y y) ∨ (k x y) = (M.op x x) := by
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
        have b1e57 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e60 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e61 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
        clear b1e57
        have b1e62 : (k x y) = (M.op x x) := by grind
        clear b1e55
        have b1e63 : (M.op (σ x) (σ y)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e61
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e61
          | exact resolve b1e61 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e64 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e63
             have i₂ := b1e60 x
             grind)
          | exact superpose b1e60 b1e63
          | exact resolve b1e63 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63
        have b1e66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e60 (σ X0)
             grind)
          | exact superpose b1e60 b1e18
          | exact resolve b1e18 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e66 X0
             have i₂ := b1e60 X0
             grind)
          | exact superpose b1e60 b1e66
          | exact resolve b1e66 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60 b1e66
        have b1e82 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e16 (σ x) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) X0
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e84 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e82 X0
             have i₂ := b1e64
             grind)
          | exact superpose b1e64 b1e82
          | (have j0 := b1e82 X0
             grind)
          | exact resolve b1e82 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e82
        have b1e144 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e64
             grind)
          | exact superpose b1e64 b1e23
          | exact resolve b1e23 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e3228 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e84 (σ y)
             have i₂ := b1e64
             grind)
          | exact superpose b1e64 b1e84
          | (have j0 := b1e84 (σ y)
             grind)
          | (have r₁ := b1e84 (σ y)
             have r₂ := b1e64
             grind)
          | exact resolve b1e84 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64 b1e84
        have b1e3252 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e3228
        have b1e3264 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e3252
             have i₂ := b1e73 y
             grind)
          | exact superpose b1e73 b1e3252
          | exact resolve b1e3252 b1e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3252
        have b1e3276 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e3264
             have r₂ := b1e144
             grind)
          | exact resolve b1e3264 b1e144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3264
        have b1e3285 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e3276
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e3276
          | exact resolve b1e3276 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3276
        have b1e3292 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e3285
             have i₂ := b1e62
             grind)
          | exact superpose b1e62 b1e3285
          | exact resolve b1e3285 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62 b1e3285
        have b1e3298 : (σ (M.op y y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e3292
             have i₂ := b1e73 y
             grind)
          | exact superpose b1e73 b1e3292
          | exact resolve b1e3292 b1e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73 b1e3292
        have b1e3302 : False := by grind
        exact b1e3302
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x y) = (M.op y y) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e53 : (M.op y y) ≠ (M.op y y) ∨ (k x y) = (M.op x x) := by
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
        have b2e56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : (k x y) = (M.op x x) := by grind
        clear b2e53
        have b2e59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e56 (σ X0)
             grind)
          | exact superpose b2e56 b2e18
          | exact resolve b2e18 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e59 X0
             have i₂ := b2e56 X0
             grind)
          | exact superpose b2e56 b2e59
          | exact resolve b2e59 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56 b2e59
        have b2e100 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) (σ x)
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 (σ x) X0
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e201 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e66 x
             grind)
          | exact superpose b2e66 b2e22
          | exact resolve b2e22 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e5485 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e100 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e100
        have b2e5486 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e5485
             have r₂ := b2e21
             grind)
          | exact resolve b2e5485 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5485
        have b2e5496 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e5486
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e5486
          | exact resolve b2e5486 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5486
        have b2e5502 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e5496
             have i₂ := b2e57
             grind)
          | exact superpose b2e57 b2e5496
          | exact resolve b2e5496 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57 b2e5496
        have b2e5506 : False := by grind
        exact b2e5506
  · rcases eq_or_ne (M.op x x) (M.op x y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op y y) := by grind
        have b3e21 : (M.op x y) = (M.op x x) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e59 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
        have b3e62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e63 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b3e59
        have b3e65 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e63
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e63
          | exact resolve b3e63 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e62 (σ X0)
             grind)
          | exact superpose b3e62 b3e18
          | exact resolve b3e18 b3e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e68 X0
             have i₂ := b3e62 X0
             grind)
          | exact superpose b3e62 b3e68
          | exact resolve b3e68 b3e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e83 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ (M.op X0 X0) = (M.op x X0) ∨ (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e16 x X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 x X0
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e86 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e65
             grind)
          | exact superpose b3e65 b3e15
          | exact resolve b3e15 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65
        have b3e91 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b3e86
        have b3e93 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e91
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e91
          | exact resolve b3e91 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e91
        have b3e94 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e93
             have i₂ := b3e62 x
             grind)
          | exact superpose b3e62 b3e93
          | exact resolve b3e93 b3e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62 b3e93
        have b3e95 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e94
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e94
          | exact resolve b3e94 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e94
        have b3e311 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e75 y
             grind)
          | exact superpose b3e75 b3e23
          | exact resolve b3e23 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e75
        have b3e1468 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (k x y) := by
          first
          | (have j0 := b3e83 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e83
        have b3e1469 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b3e1468
             have r₂ := b3e20
             grind)
          | exact resolve b3e1468 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1468
        have b3e1482 : (σ (M.op x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e95
             have i₂ := b3e1469
             grind)
          | exact superpose b3e1469 b3e95
          | exact resolve b3e95 b3e1469
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e95 b3e1469
        have b3e1486 : False := by grind
        exact b3e1486
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op x x) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
          have b4e74 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e76 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e74 (σ X0)
               grind)
            | exact superpose b4e74 b4e19
            | exact resolve b4e19 b4e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e85 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e76 X0
               have i₂ := b4e74 X0
               grind)
            | exact superpose b4e74 b4e76
            | exact resolve b4e76 b4e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74 b4e76
          have b4e169 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e28
               have i₂ := b4e85 x
               grind)
            | exact superpose b4e85 b4e28
            | (have r₁ := b4e28
               have r₂ := b4e85 x
               grind)
            | exact resolve b4e28 b4e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e85
          have b4e179 : False := by grind
          exact b4e179
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b5e22 : (M.op x y) = (M.op x x) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op y y) ≠ (M.op x x) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e71 (σ X0)
               grind)
            | exact superpose b5e71 b5e19
            | exact resolve b5e19 b5e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e73 X0
               have i₂ := b5e71 X0
               grind)
            | exact superpose b5e71 b5e73
            | exact resolve b5e73 b5e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71 b5e73
          have b5e90 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by
            first
            | (have i₁ := b5e17 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 x x
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e95 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
          clear b5e90
          have b5e96 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b5e95
               have r₂ := b5e25
               grind)
            | exact resolve b5e95 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e95
          have b5e116 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ y) (σ y)
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
          have b5e156 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e82 y
               grind)
            | exact superpose b5e82 b5e23
            | exact resolve b5e23 b5e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e82
          have b5e5707 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e116 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e116
          have b5e5708 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e5707
               have r₂ := b5e24
               grind)
            | exact resolve b5e5707 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5707
          have b5e5709 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e5708
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e5708
            | exact resolve b5e5708 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5708
          have b5e5710 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e5709
               have i₂ := b5e96
               grind)
            | exact superpose b5e96 b5e5709
            | exact resolve b5e5709 b5e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e96 b5e5709
          have b5e5711 : False := by grind
          exact b5e5711
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e21 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e55 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
        have b6e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e58 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b6e55
        have b6e59 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e58
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e58
          | exact resolve b6e58 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e78 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e59
             grind)
          | exact superpose b6e59 b6e15
          | exact resolve b6e15 b6e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e83 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e78
        have b6e84 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e83
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e83
          | exact resolve b6e83 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e85 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e84
             have i₂ := b6e57 x
             grind)
          | exact superpose b6e57 b6e84
          | exact resolve b6e84 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57 b6e84
        have b6e146 : (k x y) = (τ (σ (M.op x x))) := by
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
        have b6e147 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b6e146
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e146
          | exact resolve b6e146 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e146
        have b6e210 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
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
        have b6e211 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
        clear b6e210
        have b6e213 : (M.op x y) = (M.op y y) := by
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b7e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e71 (σ X0)
               grind)
            | exact superpose b7e71 b7e19
            | exact resolve b7e19 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e73 X0
               have i₂ := b7e71 X0
               grind)
            | exact superpose b7e71 b7e73
            | exact resolve b7e73 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71 b7e73
          have b7e92 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) (σ x)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e95 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e92
          have b7e96 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e95
               have r₂ := b7e25
               grind)
            | exact resolve b7e95 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e95
          have b7e97 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e96
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e96
            | exact resolve b7e96 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96
          have b7e98 : (σ (k x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e97
               have i₂ := b7e82 y
               grind)
            | exact superpose b7e82 b7e97
            | exact resolve b7e97 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82 b7e97
          have b7e103 : (k x y) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e98
               grind)
            | exact superpose b7e98 b7e14
            | exact resolve b7e14 b7e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98
          have b7e104 : (M.op y y) = (k x y) := by
            first
            | (have i₁ := b7e103
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e103
            | exact resolve b7e103 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e103
          have b7e167 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e104
               grind)
            | exact superpose b7e104 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e104
          have b7e168 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b7e167
          have b7e170 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b7e168
               have r₂ := b7e21
               grind)
            | exact resolve b7e168 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e168
          have b7e172 : False := by grind
          exact b7e172
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e122 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ y) (σ y)
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
          have b8e6760 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e122 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e122
          have b8e6761 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e6760
               have r₂ := b8e24
               grind)
            | exact resolve b8e6760 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6760
          have b8e6762 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e6761
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e6761
            | exact resolve b8e6761 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6761
          have b8e6766 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e6762
               grind)
            | exact superpose b8e6762 b8e20
            | exact resolve b8e20 b8e6762
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6762
          have b8e6922 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e6766
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e6766
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e6766 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6766
          have b8e6923 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e6922
          have b8e6925 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b8e6923
               have r₂ := b8e21
               grind)
            | exact resolve b8e6923 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6923
          have b8e6928 : False := by grind
          exact b8e6928

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
      have b0e581550 : ∀ X0 X1 X2 : G, (σ (M.op X2 y)) ≠ (M.op X1 (σ (M.op X0 y))) := by
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
      have b0e581586 : ∀ X0 X1 : G, (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) = (M.op X1 (σ (M.op X0 y))) := by
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
      have b0e581688 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (M.op X1 (σ (M.op X0 y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e581586 X0 X1
           have i₂ := b0e79465 X0
           grind)
        | exact superpose b0e79465 b0e581586
        | exact resolve b0e581586 b0e79465
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79465 b0e581586
      have b0e581736 : False := by
        have f581736_10 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (M.op X1 (σ (M.op X0 y))) := by
          intro X0 X1
          grind
        have f581736_11 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 y))) ≠ (σ (M.op X2 y)) := by
          intro X0 X1 X2
          grind
        have f581736_20 : False := by
          first
          | (have r₁ := f581736_10 x x
             have r₂ := f581736_11 x x x
             grind)
          | exact resolve f581736_10 f581736_11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        exact f581736_20
      exact b0e581736
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
