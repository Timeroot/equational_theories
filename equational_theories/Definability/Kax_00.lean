import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1043`: `x = x ◇ ((y ◇ (x ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_x_y_pxy_Equation1043 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1043 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1043.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e33 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 y) x)) := by
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
      have b0e35 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
           have i₂ := b0e11 X0 X2 X3
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 y) (M.op x x)) := by
        intro X0
        first
        | (have i₁ := b0e11 (M.op X0 y) x x
           have i₂ := b0e33 X0
           grind)
        | exact superpose b0e33 b0e11
        | exact resolve b0e11 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 X1 : G, x = (M.op x (M.op (M.op X0 x) (M.op (M.op X1 y) x))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 x X0 (M.op (M.op X1 y) x)
           have i₂ := b0e33 X1
           grind)
        | exact superpose b0e33 b0e11
        | exact resolve b0e11 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e39 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 y) y) := by
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
      have b0e113 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
           have i₂ := b0e35 X0 X1 X2 X3
           grind)
        | exact superpose b0e35 b0e11
        | exact resolve b0e11 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e117 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e113 X0 X1 x x
           have i₂ := b0e11 X0 x x
           grind)
        | exact superpose b0e11 b0e113
        | exact resolve b0e113 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e113
      have b0e128 : y = (M.op y x) := by
        first
        | (have i₁ := b0e117 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e117
        | exact resolve b0e117 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117
      have b0e170 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) x)) := by
        intro X0
        first
        | (have i₁ := b0e11 y X0 x
           have i₂ := b0e128
           grind)
        | exact superpose b0e128 b0e11
        | exact resolve b0e11 b0e128
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e608 : ∀ X0 : G, x = (M.op x (M.op y (M.op (M.op X0 y) x))) := by
        intro X0
        first
        | (have i₁ := b0e38 y X0
           have i₂ := b0e128
           grind)
        | exact superpose b0e128 b0e38
        | exact resolve b0e38 b0e128
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e128
      have b0e631 : x = (M.op x y) := by
        first
        | (have i₁ := b0e608 x
           have i₂ := b0e170 x
           grind)
        | exact superpose b0e170 b0e608
        | exact resolve b0e608 b0e170
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e608
      have b0e635 : y = (M.op y (M.op x x)) := by
        first
        | (have i₁ := b0e170 x
           have i₂ := b0e631
           grind)
        | exact superpose b0e631 b0e170
        | exact resolve b0e170 b0e631
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e170
      have b0e650 : y = (M.op y y) := by
        first
        | (have i₁ := b0e635
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e635
        | exact resolve b0e635 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e635
      have b0e690 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) y)) := by
        intro X0
        first
        | (have i₁ := b0e11 y X0 y
           have i₂ := b0e650
           grind)
        | exact superpose b0e650 b0e11
        | exact resolve b0e11 b0e650
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e701 : ∀ X0 : G, y = (M.op y (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e690 X0
           have i₂ := b0e39 X0
           grind)
        | exact superpose b0e39 b0e690
        | exact resolve b0e690 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e690
      have b0e812 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (M.op y y))) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e35 X0 X1 y y
           have i₂ := b0e701 X0
           grind)
        | exact superpose b0e701 b0e35
        | exact resolve b0e35 b0e701
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e813 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 y y
           have i₂ := b0e701 X0
           grind)
        | exact superpose b0e701 b0e11
        | exact resolve b0e11 b0e701
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e701
      have b0e826 : ∀ X0 : G, (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e813 X0
           have i₂ := b0e650
           grind)
        | exact superpose b0e650 b0e813
        | exact resolve b0e813 b0e650
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e813
      have b0e827 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) y)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e812 X0 X1
           have i₂ := b0e650
           grind)
        | exact superpose b0e650 b0e812
        | exact resolve b0e812 b0e650
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e650 b0e812
      have b0e830 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e827 X0 X1
           have i₂ := b0e826 (M.op X1 X0)
           grind)
        | exact superpose b0e826 b0e827
        | exact resolve b0e827 b0e826
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e826 b0e827
      have b0e1116 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X0 X0
           have i₂ := b0e830 X0 X1
           grind)
        | exact superpose b0e830 b0e11
        | exact resolve b0e11 b0e830
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e830
      have b0e1258 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e1116 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e1116
        | exact resolve b0e1116 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1116
      have b0e1390 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e1258 (σ x)
           grind)
        | exact superpose b0e1258 b0e18
        | exact resolve b0e18 b0e1258
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1258
      have b0e1399 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e1390
           have i₂ := b0e631
           grind)
        | exact superpose b0e631 b0e1390
        | exact resolve b0e1390 b0e631
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e631 b0e1390
      have b0e1400 : False := by grind
      exact b0e1400
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : x = (k x y) := by grind
        have b1e37 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e40 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e37
        have b1e42 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e40
             have r₂ := b1e21
             grind)
          | exact resolve b1e40 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e44 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e42
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e42
          | exact resolve b1e42 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e45 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e44
             have i₂ := b1e25
             grind)
          | exact superpose b1e25 b1e44
          | exact resolve b1e44 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e44
        have b1e49 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e45
             grind)
          | exact superpose b1e45 b1e13
          | exact resolve b1e13 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : x = y := by
          first
          | (have i₁ := b1e49
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e49
          | exact resolve b1e49 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e68 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e50
             grind)
          | exact superpose b1e50 b1e24
          | exact resolve b1e24 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e50
        have b1e70 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e68
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e68
          | exact resolve b1e68 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e71 : False := by grind
        exact b1e71
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e53 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
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
        have b2e175 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e53 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e176 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e175
             have r₂ := b2e22
             grind)
          | exact resolve b2e175 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e175
        have b2e177 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e176
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e176
          | exact resolve b2e176 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e176
        have b2e178 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e177
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e177
          | exact resolve b2e177 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e177
        have b2e179 : False := by grind
        exact b2e179
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : (σ x) = (k (σ x) (σ y)) := by grind
        have b3e26 : (σ x) = (σ (k x y)) := by
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
        have b3e27 : (k x y) = (τ (σ x)) := by
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
        have b3e28 : x = (k x y) := by
          first
          | (have i₁ := b3e27
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e27
          | exact resolve b3e27 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e48 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
        have b3e54 : y = (M.op x x) ∨ y = (k x y) := by grind
        clear b3e48
        have b3e55 : y = (k x y) := by
          first
          | (have r₁ := b3e54
             have r₂ := b3e20
             grind)
          | exact resolve b3e54 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e56 : x = y := by
          first
          | (have i₁ := b3e55
             have i₂ := b3e28
             grind)
          | exact superpose b3e28 b3e55
          | exact resolve b3e55 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e55
        have b3e59 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e24
          | exact resolve b3e24 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e62 : (σ x) ≠ (σ y) := by
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
        have b3e64 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e62
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e62
          | exact resolve b3e62 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56 b3e62
        have b3e65 : False := by grind
        exact b3e65
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e36 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
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
          have b5e41 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
          have b5e46 : y = (M.op x x) ∨ y = (k x y) := by grind
          clear b5e41
          have b5e47 : y = (k x y) := by
            first
            | (have r₁ := b5e46
               have r₂ := b5e21
               grind)
            | exact resolve b5e46 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e58 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
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
          have b5e99 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
               have i₂ := b5e36 X0 X1 X2 X3
               grind)
            | exact superpose b5e36 b5e13
            | exact resolve b5e13 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e103 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e99 X0 X1 x x
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e99
            | exact resolve b5e99 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e99
          have b5e196 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e58 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e197 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e196
               have r₂ := b5e24
               grind)
            | exact resolve b5e196 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e196
          have b5e198 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e197
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e197
            | exact resolve b5e197 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e197
          have b5e199 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e198
               have i₂ := b5e47
               grind)
            | exact superpose b5e47 b5e198
            | exact resolve b5e198 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e198
          have b5e202 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e103 (σ y) (σ x)
               have i₂ := b5e199
               grind)
            | exact superpose b5e199 b5e103
            | exact resolve b5e103 b5e199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e199
          have b5e325 : (σ y) = (k (σ y) (σ y)) := by grind
          have b5e336 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b5e325
               have i₂ := b5e19 y y
               grind)
            | exact superpose b5e19 b5e325
            | exact resolve b5e325 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e325
          have b5e377 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b5e14 (k y y)
               have i₂ := b5e336
               grind)
            | exact superpose b5e336 b5e14
            | exact resolve b5e14 b5e336
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e336
          have b5e392 : y = (k y y) := by
            first
            | (have i₁ := b5e377
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e377
            | exact resolve b5e377 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e377
          have b5e422 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e18 y y
               have i₂ := b5e392
               grind)
            | exact superpose b5e392 b5e18
            | (have j0 := b5e18 y y
               grind)
            | exact resolve b5e18 b5e392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e392
          have b5e423 : y = (M.op y y) := by grind
          clear b5e422
          have b5e473 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) y)) := by
            intro X0
            first
            | (have i₁ := b5e13 y X0 y
               have i₂ := b5e423
               grind)
            | exact superpose b5e423 b5e13
            | exact resolve b5e13 b5e423
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e484 : ∀ X0 : G, y = (M.op y (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e473 X0
               have i₂ := b5e103 y X0
               grind)
            | exact superpose b5e103 b5e473
            | exact resolve b5e473 b5e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103 b5e473
          have b5e513 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (M.op y y))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e36 X0 X1 y y
               have i₂ := b5e484 X0
               grind)
            | exact superpose b5e484 b5e36
            | exact resolve b5e36 b5e484
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e514 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y y
               have i₂ := b5e484 X0
               grind)
            | exact superpose b5e484 b5e13
            | exact resolve b5e13 b5e484
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e484
          have b5e527 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e514 X0
               have i₂ := b5e423
               grind)
            | exact superpose b5e423 b5e514
            | exact resolve b5e514 b5e423
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e514
          have b5e528 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) y)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e513 X0 X1
               have i₂ := b5e423
               grind)
            | exact superpose b5e423 b5e513
            | exact resolve b5e513 b5e423
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e423 b5e513
          have b5e530 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e528 X0 X1
               have i₂ := b5e527 (M.op X1 X0)
               grind)
            | exact superpose b5e527 b5e528
            | exact resolve b5e528 b5e527
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e527 b5e528
          have b5e904 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 X0
               have i₂ := b5e530 X0 X1
               grind)
            | exact superpose b5e530 b5e13
            | exact resolve b5e13 b5e530
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e530
          have b5e1052 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e904 (σ y) X0
               have i₂ := b5e202
               grind)
            | exact superpose b5e202 b5e904
            | exact resolve b5e904 b5e202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e202 b5e904
          have b5e1124 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1052 (σ x)
               grind)
            | exact superpose b5e1052 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e1052 (σ x)
               grind)
            | exact resolve b5e24 b5e1052
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1052
          have b5e1128 : False := by grind
          exact b5e1128
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
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
        have b6e26 : (k x y) = (τ (σ x)) := by
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
        have b6e27 : x = (k x y) := by
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
        have b6e72 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
        have b6e79 : x = (M.op x y) ∨ y = (M.op x x) := by grind
        clear b6e72
        have b6e82 : y = (M.op x x) := by
          first
          | (have r₁ := b6e79
             have r₂ := b6e21
             grind)
          | exact resolve b6e79 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e85 : False := by grind
        exact b6e85
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
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
          have b7e38 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e41 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e38
          have b7e42 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e41
               have r₂ := b7e23
               grind)
            | exact resolve b7e41 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e43 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e42
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e42
            | exact resolve b7e42 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e46 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e43
               grind)
            | exact superpose b7e43 b7e14
            | exact resolve b7e14 b7e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e47 : y = (k x y) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e46
            | exact resolve b7e46 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e63 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e47
               grind)
            | exact superpose b7e47 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e64 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e21
               grind)
            | exact resolve b7e63 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e66 : y = (M.op x y) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e22
               grind)
            | exact resolve b7e64 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e92 : ∀ X0 X1 : G, y = (M.op y (M.op y (M.op (M.op X0 (M.op y X1)) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e30 y x X0 X1
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e30
            | exact resolve b7e30 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e104 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
               have i₂ := b7e30 X0 X1 X2 X3
               grind)
            | exact superpose b7e30 b7e13
            | exact resolve b7e13 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e108 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e104 X0 X1 x x
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e104
            | exact resolve b7e104 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e104
          have b7e111 : y = (M.op y y) := by
            first
            | (have i₁ := b7e92 x x
               have i₂ := b7e13 y x x
               grind)
            | exact superpose b7e13 b7e92
            | exact resolve b7e92 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e135 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) y)) := by
            intro X0
            first
            | (have i₁ := b7e13 y X0 y
               have i₂ := b7e111
               grind)
            | exact superpose b7e111 b7e13
            | exact resolve b7e13 b7e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e136 : ∀ X0 : G, y = (M.op y (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b7e135 X0
               have i₂ := b7e108 y X0
               grind)
            | exact superpose b7e108 b7e135
            | exact resolve b7e135 b7e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e108 b7e135
          have b7e193 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 y y
               have i₂ := b7e136 X0
               grind)
            | exact superpose b7e136 b7e13
            | exact resolve b7e13 b7e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e136
          have b7e202 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b7e193 X0
               have i₂ := b7e111
               grind)
            | exact superpose b7e111 b7e193
            | exact resolve b7e193 b7e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111 b7e193
          have b7e304 : x ≠ x := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e202 x
               grind)
            | exact superpose b7e202 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e202 x
               grind)
            | exact resolve b7e22 b7e202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e202
          have b7e305 : False := by grind
          exact b7e305
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e55 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
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
          have b8e160 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e55 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e161 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e160
               have r₂ := b8e24
               grind)
            | exact resolve b8e160 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160
          have b8e162 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e161
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e161
            | exact resolve b8e161 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e161
          have b8e163 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e162
               grind)
            | exact superpose b8e162 b8e20
            | exact resolve b8e20 b8e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e162
          have b8e314 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e163
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e163
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e163 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e163
          have b8e315 : y = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b8e314
          have b8e319 : x = (M.op x y) := by
            first
            | (have r₁ := b8e315
               have r₂ := b8e21
               grind)
            | exact resolve b8e315 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e315
          have b8e323 : False := by grind
          exact b8e323

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_x_pxy_pxy_pyx_Equation1061 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x x) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) x)) = X0 := by
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
      have b0e33 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
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
      have b0e35 : ∀ X0 : G, (M.op X0 x) = X0 := by
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
      have b0e39 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
      have b0e41 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b0e14 x X0
           have i₂ := b0e35 x
           grind)
        | exact superpose b0e35 b0e14
        | (have j0 := b0e14 x X0
           grind)
        | (have r₁ := b0e14 x x
           have r₂ := b0e35 x
           grind)
        | exact resolve b0e14 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e42 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
        intro X0
        first
        | (have j0 := b0e41 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e44 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b0e39 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e66 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 x X0
           have i₂ := b0e44 (σ X0)
           grind)
        | exact superpose b0e44 b0e17
        | exact resolve b0e17 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e68 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e66 X0
           have i₂ := b0e42 X0
           grind)
        | exact superpose b0e42 b0e66
        | exact resolve b0e66 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e66
      have b0e598 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e68 y
           grind)
        | exact superpose b0e68 b0e18
        | (have r₁ := b0e18
           have r₂ := b0e68 y
           grind)
        | exact resolve b0e18 b0e68
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e612 : False := by grind
      exact b0e612
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op x x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) x)) = X0 := by
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
        have b1e31 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e26 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e26
          | exact resolve b1e26 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e32 : ∀ X0 : G, (M.op X0 x) = X0 := by
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
        have b1e37 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b1e15 x X0
             have i₂ := b1e32 x
             grind)
          | exact superpose b1e32 b1e15
          | (have j0 := b1e15 x X0
             grind)
          | (have r₁ := b1e15 x x
             have r₂ := b1e32 x
             grind)
          | exact resolve b1e15 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e38 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b1e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e41 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e16 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) x
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e46 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e41
        have b1e47 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e46
             have r₂ := b1e21
             grind)
          | exact resolve b1e46 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e48 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e47
          | exact resolve b1e47 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e49 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b1e48
             have i₂ := b1e38 y
             grind)
          | exact superpose b1e38 b1e48
          | exact resolve b1e48 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38 b1e48
        have b1e50 : False := by grind
        exact b1e50
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e25 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e25 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e25
          | exact resolve b2e25 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e30 : ∀ X0 : G, (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e29 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e29
          | exact resolve b2e29 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x X0))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 x
             have i₂ := b2e30 (M.op X0 (M.op x X0))
             grind)
          | exact superpose b2e30 b2e12
          | exact resolve b2e12 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (k (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 (M.op (M.op X0 (M.op X1 X0)) X1) X2
             have i₂ := b2e12 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 (M.op (M.op X0 (M.op X1 X0)) X1) X2
             grind)
          | (have r₁ := b2e15 (M.op (M.op X1 (M.op X2 X1)) X2) X1
             have r₂ := b2e12 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b2e15 x X0
             have i₂ := b2e30 x
             grind)
          | exact superpose b2e30 b2e15
          | (have j0 := b2e15 x X0
             grind)
          | (have r₁ := b2e15 x x
             have r₂ := b2e30 x
             grind)
          | exact resolve b2e15 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b2e35 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e37 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e34 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e40 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e16 X0 x
             have i₂ := b2e30 X0
             grind)
          | exact superpose b2e30 b2e16
          | (have j0 := b2e16 X0 x
             grind)
          | (have r₁ := b2e16 X0 x
             have r₂ := b2e30 X0
             grind)
          | exact resolve b2e16 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b2e40 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e105 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e24 X1 X0
             grind)
          | exact superpose b2e24 b2e13
          | exact resolve b2e13 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24
        have b2e139 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) x) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e41 (σ x)
             grind)
          | exact superpose b2e41 b2e21
          | (have j1 := b2e41 (σ x)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e41 (σ x)
             grind)
          | exact resolve b2e21 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e144 : (σ x) = (k (σ x) x) := by grind
        clear b2e139
        have b2e338 : (k x (τ x)) = (τ (σ x)) := by
          first
          | (have i₁ := b2e105 x x
             have i₂ := b2e144
             grind)
          | exact superpose b2e144 b2e105
          | exact resolve b2e105 b2e144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e105 b2e144
        have b2e349 : x = (k x (τ x)) := by
          first
          | (have i₁ := b2e338
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e338
          | exact resolve b2e338 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e338
        have b2e351 : x = (M.op x (τ x)) := by
          first
          | (have i₁ := b2e349
             have i₂ := b2e36 (τ x)
             grind)
          | exact superpose b2e36 b2e349
          | exact resolve b2e349 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e349
        have b2e388 : ∀ X0 : G, (k (M.op (M.op (τ x) x) x) X0) = (M.op (M.op (M.op (τ x) x) x) X0) := by
          intro X0
          first
          | (have i₁ := b2e37 (τ x) x x
             have i₂ := b2e351
             grind)
          | exact superpose b2e351 b2e37
          | exact resolve b2e37 b2e351
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37 b2e351
        have b2e418 : ∀ X0 : G, (k (M.op (τ x) x) X0) = (M.op (M.op (τ x) x) X0) := by
          intro X0
          first
          | (have i₁ := b2e388 X0
             have i₂ := b2e30 (M.op (τ x) x)
             grind)
          | exact superpose b2e30 b2e388
          | exact resolve b2e388 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e388
        have b2e419 : ∀ X0 : G, (k (τ x) X0) = (M.op (τ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e418 X0
             have i₂ := b2e30 (τ x)
             grind)
          | exact superpose b2e30 b2e418
          | exact resolve b2e418 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e418
        have b2e490 : ∀ X0 : G, (k x (σ X0)) = (σ (M.op (τ x) X0)) := by
          intro X0
          first
          | (have i₁ := b2e23 x X0
             have i₂ := b2e419 X0
             grind)
          | exact superpose b2e419 b2e23
          | exact resolve b2e23 b2e419
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e419
        have b2e497 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op (τ x) X0)) := by
          intro X0
          first
          | (have i₁ := b2e490 X0
             have i₂ := b2e36 (σ X0)
             grind)
          | exact superpose b2e36 b2e490
          | exact resolve b2e490 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e490
        have b2e1054 : (M.op x (σ x)) = (σ (τ x)) := by
          first
          | (have i₁ := b2e497 x
             have i₂ := b2e30 (τ x)
             grind)
          | exact superpose b2e30 b2e497
          | exact resolve b2e497 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e497
        have b2e1075 : x = (M.op x (σ x)) := by
          first
          | (have i₁ := b2e1054
             have i₂ := b2e14 x
             grind)
          | exact superpose b2e14 b2e1054
          | exact resolve b2e1054 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1054
        have b2e1219 : ∀ X0 : G, (M.op X0 (M.op (σ x) x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e32 (σ x) X0
             have i₂ := b2e1075
             grind)
          | exact superpose b2e1075 b2e32
          | exact resolve b2e32 b2e1075
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e1075
        have b2e1238 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1219 X0
             have i₂ := b2e30 (σ x)
             grind)
          | exact superpose b2e30 b2e1219
          | exact resolve b2e1219 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30 b2e1219
        have b2e1416 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e1238 (σ x)
             grind)
          | exact superpose b2e1238 b2e21
          | (have r₁ := b2e21
             have r₂ := b2e1238 (σ x)
             grind)
          | exact resolve b2e21 b2e1238
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1238
        have b2e1424 : False := by grind
        exact b2e1424
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e27 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ x)) (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ x) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e27 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e27
          | exact resolve b3e27 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e32 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
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
        have b3e37 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e15 (σ x) X0
             have i₂ := b3e32 (σ x)
             grind)
          | exact superpose b3e32 b3e15
          | (have j0 := b3e15 (σ x) X0
             grind)
          | (have r₁ := b3e15 (σ x) x
             have r₂ := b3e32 (σ x)
             grind)
          | exact resolve b3e15 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e38 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b3e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e46 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) := by
          first
          | (have i₁ := b3e16 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 x x
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : x = (M.op x x) ∨ x = (k x y) := by grind
        clear b3e46
        have b3e54 : x = (k x y) := by
          first
          | (have r₁ := b3e53
             have r₂ := b3e20
             grind)
          | exact resolve b3e53 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e64 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 x X0
             have i₂ := b3e38 (σ X0)
             grind)
          | exact superpose b3e38 b3e18
          | exact resolve b3e18 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e843 : (σ x) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e64 y
             grind)
          | exact superpose b3e64 b3e23
          | exact resolve b3e23 b3e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e64
        have b3e867 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e843
             have i₂ := b3e54
             grind)
          | exact superpose b3e54 b3e843
          | exact resolve b3e843 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54 b3e843
        have b3e868 : False := by grind
        exact b3e868
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x y) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (σ x) ≠ (σ x) := by
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
          have b4e27 : False := by grind
          exact b4e27
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b5e28 : ∀ X0 : G, (M.op X0 (M.op (M.op y x) x)) = X0 := by
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
          have b5e30 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X0 (M.op X2 (M.op X0 X2))
               have i₂ := b5e13 X0 X2 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x (M.op y x)
               have i₂ := b5e28 x
               grind)
            | exact superpose b5e28 b5e13
            | exact resolve b5e13 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e95 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e30 y X0 x
               have i₂ := b5e32 y
               grind)
            | exact superpose b5e32 b5e30
            | exact resolve b5e30 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e32
          have b5e103 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e16 y X0
               have i₂ := b5e95 y
               grind)
            | exact superpose b5e95 b5e16
            | (have j0 := b5e16 y X0
               grind)
            | (have r₁ := b5e16 y x
               have r₂ := b5e95 y
               grind)
            | exact resolve b5e16 b5e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e105 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e17 X0 y
               have i₂ := b5e95 X0
               grind)
            | exact superpose b5e95 b5e17
            | (have j0 := b5e17 X0 x
               grind)
            | (have r₁ := b5e17 X0 y
               have r₂ := b5e95 X0
               grind)
            | exact resolve b5e17 b5e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e107 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op y X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 y
               have i₂ := b5e95 (M.op X0 (M.op y X0))
               grind)
            | exact superpose b5e95 b5e13
            | exact resolve b5e13 b5e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e108 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e105 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e105
          have b5e109 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b5e103 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103
          have b5e483 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 y) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X0 X1
               have i₂ := b5e108 X0
               grind)
            | exact superpose b5e108 b5e16
            | (have j0 := b5e16 X0 X1
               have j1 := b5e108 X0
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e108 X0
               grind)
            | exact resolve b5e16 b5e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e108
          have b5e500 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 y) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e483 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e483
          have b5e951 : ∀ X0 : G, (M.op X0 y) ≠ X0 ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e500 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e500
          have b5e952 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e951 X0
               grind)
            | (have r₁ := b5e951 X0
               have r₂ := b5e95 X0
               grind)
            | exact resolve b5e951 b5e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e951
          have b5e987 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e26 X0 y
               have i₂ := b5e952 (τ X0)
               grind)
            | exact superpose b5e952 b5e26
            | exact resolve b5e26 b5e952
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e952
          have b5e989 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e987 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e987
            | exact resolve b5e987 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e987
          have b5e1048 : y = (M.op y (σ y)) := by
            first
            | (have i₁ := b5e109 (σ y)
               have i₂ := b5e989 y
               grind)
            | exact superpose b5e989 b5e109
            | exact resolve b5e109 b5e989
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e109 b5e989
          have b5e1179 : ∀ X0 : G, (M.op X0 (M.op (σ y) y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e107 (σ y) X0
               have i₂ := b5e1048
               grind)
            | exact superpose b5e1048 b5e107
            | exact resolve b5e107 b5e1048
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e107 b5e1048
          have b5e1196 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1179 X0
               have i₂ := b5e95 (σ y)
               grind)
            | exact superpose b5e95 b5e1179
            | exact resolve b5e1179 b5e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95 b5e1179
          have b5e1460 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1196 (σ x)
               grind)
            | exact superpose b5e1196 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e1196 (σ x)
               grind)
            | exact resolve b5e24 b5e1196
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1196
          have b5e1465 : False := by grind
          exact b5e1465
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ x)) (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e29 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 := by
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
        have b6e30 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
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
        have b6e35 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e15 (σ x) X0
             have i₂ := b6e30 (σ x)
             grind)
          | exact superpose b6e30 b6e15
          | (have j0 := b6e15 (σ x) X0
             grind)
          | (have r₁ := b6e15 (σ x) x
             have r₂ := b6e30 (σ x)
             grind)
          | exact resolve b6e15 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e36 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b6e35 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e40 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e36 (σ X0)
             grind)
          | exact superpose b6e36 b6e18
          | exact resolve b6e18 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e374 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e30 (σ x)
             have i₂ := b6e40 x
             grind)
          | exact superpose b6e40 b6e30
          | exact resolve b6e30 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30 b6e40
        have b6e427 : (τ (σ x)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e374
             grind)
          | exact superpose b6e374 b6e13
          | exact resolve b6e13 b6e374
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e374
        have b6e429 : x = (k x x) := by
          first
          | (have i₁ := b6e427
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e427
          | exact resolve b6e427 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e427
        have b6e521 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e429
             grind)
          | exact superpose b6e429 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e429
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e429
        have b6e522 : x = (M.op x x) := by grind
        clear b6e521
        have b6e526 : False := by grind
        exact b6e526
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e34 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X0 (M.op X2 (M.op X0 X2))
               have i₂ := b7e13 X0 X2 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e87 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e34 (σ x) X0 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e34
            | exact resolve b7e34 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e365 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e34 (σ y) X0 (σ x)
               have i₂ := b7e87 (σ y)
               grind)
            | exact superpose b7e87 b7e34
            | exact resolve b7e34 b7e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e434 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e16 (σ y) X0
               have i₂ := b7e365 (σ y)
               grind)
            | exact superpose b7e365 b7e16
            | (have j0 := b7e16 (σ y) X0
               grind)
            | (have r₁ := b7e16 (σ y) x
               have r₂ := b7e365 (σ y)
               grind)
            | exact resolve b7e16 b7e365
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e451 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b7e434 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e434
          have b7e539 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 y X0
               have i₂ := b7e451 (σ X0)
               grind)
            | exact superpose b7e451 b7e19
            | exact resolve b7e19 b7e451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e451
          have b7e943 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e365 (σ y)
               have i₂ := b7e539 y
               grind)
            | exact superpose b7e539 b7e365
            | exact resolve b7e365 b7e539
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e365 b7e539
          have b7e1017 : (τ (σ y)) = (k y y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e943
               grind)
            | exact superpose b7e943 b7e14
            | exact resolve b7e14 b7e943
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e943
          have b7e1046 : y = (k y y) := by
            first
            | (have i₁ := b7e1017
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e1017
            | exact resolve b7e1017 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1017
          have b7e1109 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e1046
               grind)
            | exact superpose b7e1046 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e1046
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1046
          have b7e1110 : y = (M.op y y) := by grind
          clear b7e1109
          have b7e1251 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e34 y X0 y
               have i₂ := b7e1110
               grind)
            | exact superpose b7e1110 b7e34
            | exact resolve b7e34 b7e1110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e1261 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1251 X0
               have i₂ := b7e1110
               grind)
            | exact superpose b7e1110 b7e1251
            | exact resolve b7e1251 b7e1110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1251
          have b7e1269 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1261 X0
               have i₂ := b7e1110
               grind)
            | exact superpose b7e1110 b7e1261
            | exact resolve b7e1261 b7e1110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1110 b7e1261
          have b7e1438 : x ≠ x := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e1269 x
               grind)
            | exact superpose b7e1269 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e1269 x
               grind)
            | exact resolve b7e22 b7e1269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1269
          have b7e1439 : False := by grind
          exact b7e1439
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b8e32 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X0 (M.op X2 (M.op X0 X2))
               have i₂ := b8e13 X0 X2 X0
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          have b8e52 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e17 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e17
            | (have j0 := b8e17 X0 X1
               grind)
            | (have r₁ := b8e17 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
               have r₂ := b8e13 X0 X1 X2
               grind)
            | exact resolve b8e17 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e52 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e52
          have b8e67 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e18 (σ X1) (σ X0)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X1) (σ X1)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e73 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X2
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X1
               have j1 := b8e18 X0 X2
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e76 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e73 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e91 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 X0 X1 X0
               have i₂ := b8e18 X0 X2
               grind)
            | exact superpose b8e18 b8e32
            | (have j1 := b8e18 X0 X2
               grind)
            | exact resolve b8e32 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e211 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 (M.op (M.op X2 (M.op X3 X2)) X3)) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e53 X0 X2 X3
               grind)
            | exact superpose b8e53 b8e16
            | (have j0 := b8e16 X0 X1
               have j1 := b8e53 X0 X2 X3
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e53 X0 X1 X2
               grind)
            | exact resolve b8e16 b8e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e218 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 (M.op (M.op X2 (M.op X3 X2)) X3)) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b8e211 X0 X1 X2 X3
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e211
          have b8e389 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e76 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e666 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X0) (M.op (σ X2) (σ X0)))) = X1 ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 (σ X0) X1 (σ X2)
               have i₂ := b8e67 X2 X0
               grind)
            | exact superpose b8e67 b8e32
            | (have j1 := b8e67 X2 X0
               grind)
            | exact resolve b8e32 b8e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e673 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e67 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e674 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e673 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e673
          have b8e925 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) ≠ X0 ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e218 X0 X1 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e218
          have b8e930 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e925 X0 X1 X2
               grind)
            | (have r₁ := b8e925 X0 X1 X2
               have r₂ := b8e13 X0 X1 X2
               grind)
            | exact resolve b8e925 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e925
          have b8e949 : ∀ X0 X1 X2 : G, (k X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e930 X1 X0 (M.op X2 (M.op X0 X2))
               have i₂ := b8e13 X0 X2 X0
               grind)
            | exact superpose b8e13 b8e930
            | exact resolve b8e930 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e930
          have b8e1075 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ≠ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ∨ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
            intro X0 X1
            first
            | (have i₁ := b8e674 (M.op X0 (M.op X1 (M.op X0 X1)))
               have i₂ := b8e949 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
               grind)
            | exact superpose b8e949 b8e674
            | (have j0 := b8e674 (M.op X0 (M.op X1 (M.op X0 X1)))
               grind)
            | exact resolve b8e674 b8e949
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e674 b8e949
          have b8e1087 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
            intro X0 X1
            first
            | (have j0 := b8e1075 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1075
          have b8e3792 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b8e389 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e389
          have b8e3795 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e3792 X0
               have j1 := b8e16 X0 X0
               grind)
            | (have r₁ := b8e3792 X0
               have r₂ := b8e16 X0 x
               grind)
            | exact resolve b8e3792 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3792
          have b8e3842 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e3795 (σ X0)
               grind)
            | exact superpose b8e3795 b8e19
            | exact resolve b8e19 b8e3795
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3846 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e44 X0 X0
               have i₂ := b8e3795 (τ X0)
               grind)
            | exact superpose b8e3795 b8e44
            | exact resolve b8e44 b8e3795
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44
          have b8e3853 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e3846 X0
               have i₂ := b8e3795 X0
               grind)
            | exact superpose b8e3795 b8e3846
            | exact resolve b8e3846 b8e3795
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3846
          have b8e3857 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e3842 X0
               have i₂ := b8e3795 X0
               grind)
            | exact superpose b8e3795 b8e3842
            | exact resolve b8e3842 b8e3795
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3795 b8e3842
          have b8e4215 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (σ X0) (σ X0)
               have i₂ := b8e3857 X0
               grind)
            | exact superpose b8e3857 b8e13
            | exact resolve b8e13 b8e3857
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e8085 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e4215 (M.op X0 (M.op X1 (M.op X0 X1))) X2
               have i₂ := b8e32 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
               grind)
            | exact superpose b8e32 b8e4215
            | exact resolve b8e4215 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4215
          have b8e8350 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e8085 X0 X1 X2
               have i₂ := b8e1087 X0 X1
               grind)
            | exact superpose b8e1087 b8e8085
            | exact resolve b8e8085 b8e1087
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8085
          have b8e8378 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e8350 X0 X1 X2
               have i₂ := b8e1087 X0 X1
               grind)
            | exact superpose b8e1087 b8e8350
            | exact resolve b8e8350 b8e1087
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1087 b8e8350
          have b8e8638 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (M.op X1 (σ X0)) = X1 ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e8378 X0 X0 X1
               have i₂ := b8e91 X0 X0 X2
               grind)
            | exact superpose b8e91 b8e8378
            | (have j1 := b8e91 X0 X1 X2
               grind)
            | exact resolve b8e8378 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91 b8e8378
          have b8e64753 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 (σ X0) X1 (σ X2)
               have i₂ := b8e666 X2 (σ X0) X0
               grind)
            | exact superpose b8e666 b8e32
            | (have j1 := b8e666 X2 X1 X0
               grind)
            | exact resolve b8e32 b8e666
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e666
          have b8e65598 : ∀ X0 X1 X2 : G, (σ X2) = (σ (M.op X2 X2)) ∨ (M.op X1 (σ X0)) = X1 ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e64753 X0 X1 X2
               have i₂ := b8e3857 X2
               grind)
            | exact superpose b8e3857 b8e64753
            | (have j0 := b8e64753 X0 X1 X2
               grind)
            | exact resolve b8e64753 b8e3857
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3857 b8e64753
          have b8e99203 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e65598 x (σ x) X0
               grind)
            | exact superpose b8e65598 b8e23
            | (have j1 := b8e65598 x x X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e65598 x (σ x) x
               grind)
            | exact resolve b8e23 b8e65598
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65598
          have b8e99209 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
            intro X0
            first
            | (have j0 := b8e99203 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99203
          have b8e99846 : ∀ X0 : G, (σ (τ X0)) = (σ (τ (M.op X0 X0))) ∨ (M.op (σ x) (σ (τ X0))) = (σ (k (τ X0) x)) := by
            intro X0
            first
            | (have i₁ := b8e99209 (τ X0)
               have i₂ := b8e3853 X0
               grind)
            | exact superpose b8e3853 b8e99209
            | (have j0 := b8e99209 (τ X0)
               grind)
            | exact resolve b8e99209 b8e3853
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3853 b8e99209
          have b8e99892 : ∀ X0 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (M.op (σ x) (σ (τ X0))) = (σ (k (τ X0) x)) := by
            intro X0
            first
            | (have i₁ := b8e99846 X0
               have i₂ := b8e15 (M.op X0 X0)
               grind)
            | exact superpose b8e15 b8e99846
            | (have j0 := b8e99846 X0
               grind)
            | exact resolve b8e99846 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99846
          have b8e99895 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ x) (σ (τ X0))) = (σ (k (τ X0) x)) := by
            intro X0
            first
            | (have i₁ := b8e99892 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e99892
            | (have j0 := b8e99892 X0
               grind)
            | exact resolve b8e99892 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99892
          have b8e99896 : ∀ X0 : G, (M.op (σ x) (σ (τ X0))) = (k X0 (σ x)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e99895 X0
               have i₂ := b8e25 X0 x
               grind)
            | exact superpose b8e25 b8e99895
            | (have j0 := b8e99895 X0
               grind)
            | exact resolve b8e99895 b8e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25 b8e99895
          have b8e99897 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e99896 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e99896
            | (have j0 := b8e99896 X0
               grind)
            | exact resolve b8e99896 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99896
          have b8e99963 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X0 X1 X0
               have i₂ := b8e99897 X0
               grind)
            | exact superpose b8e99897 b8e32
            | (have j1 := b8e99897 X0
               grind)
            | exact resolve b8e32 b8e99897
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99897
          have b8e110430 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X0 X1 X0
               have i₂ := b8e99963 X0 X0
               grind)
            | exact superpose b8e99963 b8e32
            | (have j1 := b8e99963 X0 X1
               grind)
            | exact resolve b8e32 b8e99963
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99963
          have b8e110622 : ∀ X0 X1 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (M.op X1 (σ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 x
               have i₂ := b8e110430 (σ X0) X1
               grind)
            | exact superpose b8e110430 b8e19
            | (have j1 := b8e110430 (σ X0) X1
               grind)
            | exact resolve b8e19 b8e110430
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110430
          have b8e111964 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b8e20
               have i₂ := b8e110622 y X0
               grind)
            | exact superpose b8e110622 b8e20
            | (have j1 := b8e110622 y X0
               grind)
            | exact resolve b8e20 b8e110622
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110622
          have b8e113981 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k y X0) = (M.op X0 y) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e8638 y (σ x) X0
               grind)
            | exact superpose b8e8638 b8e24
            | (have j1 := b8e8638 y x X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e8638 y (σ x) x
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e8638 (σ x) x (σ y)
               grind)
            | exact resolve b8e24 b8e8638
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8638
          have b8e113984 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b8e113981 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113981
          have b8e114001 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b8e111964 X0
               have i₂ := b8e113984 x
               grind)
            | exact superpose b8e113984 b8e111964
            | (have j0 := b8e111964 X0
               have j1 := b8e113984 x
               grind)
            | exact resolve b8e111964 b8e113984
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e111964 b8e113984
          have b8e114048 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op y x) := by
            intro X0
            first
            | (have j0 := b8e114001 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e114001
          have b8e115240 : (σ x) ≠ (σ x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e114048 (σ x)
               grind)
            | exact superpose b8e114048 b8e24
            | (have r₁ := b8e24
               have r₂ := b8e114048 (σ x)
               grind)
            | exact resolve b8e24 b8e114048
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e114048
          have b8e115290 : y = (M.op y x) := by grind
          clear b8e115240
          have b8e115308 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = X0 := by
            intro X0
            first
            | (have i₁ := b8e32 y X0 x
               have i₂ := b8e115290
               grind)
            | exact superpose b8e115290 b8e32
            | exact resolve b8e32 b8e115290
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e115290
          have b8e116441 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b8e32 x X0 y
               have i₂ := b8e115308 x
               grind)
            | exact superpose b8e115308 b8e32
            | exact resolve b8e32 b8e115308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32 b8e115308
          have b8e118169 : x ≠ x := by
            first
            | (have i₁ := b8e21
               have i₂ := b8e116441 x
               grind)
            | exact superpose b8e116441 b8e21
            | (have r₁ := b8e21
               have r₂ := b8e116441 x
               grind)
            | exact resolve b8e21 b8e116441
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e116441
          have b8e118170 : False := by grind
          exact b8e118170

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_x_pxy_x_pyx_Equation1061 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x x) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) x)) = X0 := by
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
      have b0e33 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
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
      have b0e35 : ∀ X0 : G, (M.op X0 x) = X0 := by
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
      have b0e39 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
      have b0e41 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b0e14 x X0
           have i₂ := b0e35 x
           grind)
        | exact superpose b0e35 b0e14
        | (have j0 := b0e14 x X0
           grind)
        | (have r₁ := b0e14 x x
           have r₂ := b0e35 x
           grind)
        | exact resolve b0e14 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e42 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
        intro X0
        first
        | (have j0 := b0e41 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e44 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b0e39 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e66 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 x X0
           have i₂ := b0e44 (σ X0)
           grind)
        | exact superpose b0e44 b0e17
        | exact resolve b0e17 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e68 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e66 X0
           have i₂ := b0e42 X0
           grind)
        | exact superpose b0e42 b0e66
        | exact resolve b0e66 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e66
      have b0e598 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e68 y
           grind)
        | exact superpose b0e68 b0e18
        | (have r₁ := b0e18
           have r₂ := b0e68 y
           grind)
        | exact resolve b0e18 b0e68
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e612 : False := by grind
      exact b0e612
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op x x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) x)) = X0 := by
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
        have b1e31 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e26 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e26
          | exact resolve b1e26 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e32 : ∀ X0 : G, (M.op X0 x) = X0 := by
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
        have b1e37 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b1e15 x X0
             have i₂ := b1e32 x
             grind)
          | exact superpose b1e32 b1e15
          | (have j0 := b1e15 x X0
             grind)
          | (have r₁ := b1e15 x x
             have r₂ := b1e32 x
             grind)
          | exact resolve b1e15 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e38 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b1e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e41 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e46 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e41
        have b1e47 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e46
             have r₂ := b1e21
             grind)
          | exact resolve b1e46 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e48 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e47
          | exact resolve b1e47 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e49 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b1e48
             have i₂ := b1e38 y
             grind)
          | exact superpose b1e38 b1e48
          | exact resolve b1e48 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38 b1e48
        have b1e50 : False := by grind
        exact b1e50
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e25 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e25 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e25
          | exact resolve b2e25 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e30 : ∀ X0 : G, (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e29 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e29
          | exact resolve b2e29 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x X0))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 x
             have i₂ := b2e30 (M.op X0 (M.op x X0))
             grind)
          | exact superpose b2e30 b2e12
          | exact resolve b2e12 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (k (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 (M.op (M.op X0 (M.op X1 X0)) X1) X2
             have i₂ := b2e12 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 (M.op (M.op X0 (M.op X1 X0)) X1) X2
             grind)
          | (have r₁ := b2e15 (M.op (M.op X1 (M.op X2 X1)) X2) X1
             have r₂ := b2e12 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b2e15 x X0
             have i₂ := b2e30 x
             grind)
          | exact superpose b2e30 b2e15
          | (have j0 := b2e15 x X0
             grind)
          | (have r₁ := b2e15 x x
             have r₂ := b2e30 x
             grind)
          | exact resolve b2e15 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b2e35 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e37 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e34 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e40 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e16 X0 x
             have i₂ := b2e30 X0
             grind)
          | exact superpose b2e30 b2e16
          | (have j0 := b2e16 X0 x
             grind)
          | (have r₁ := b2e16 X0 x
             have r₂ := b2e30 X0
             grind)
          | exact resolve b2e16 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b2e40 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e105 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e24 X1 X0
             grind)
          | exact superpose b2e24 b2e13
          | exact resolve b2e13 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24
        have b2e139 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) x) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e41 (σ x)
             grind)
          | exact superpose b2e41 b2e21
          | (have j1 := b2e41 (σ x)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e41 (σ x)
             grind)
          | exact resolve b2e21 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e144 : (σ x) = (k (σ x) x) := by grind
        clear b2e139
        have b2e338 : (k x (τ x)) = (τ (σ x)) := by
          first
          | (have i₁ := b2e105 x x
             have i₂ := b2e144
             grind)
          | exact superpose b2e144 b2e105
          | exact resolve b2e105 b2e144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e105 b2e144
        have b2e349 : x = (k x (τ x)) := by
          first
          | (have i₁ := b2e338
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e338
          | exact resolve b2e338 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e338
        have b2e351 : x = (M.op x (τ x)) := by
          first
          | (have i₁ := b2e349
             have i₂ := b2e36 (τ x)
             grind)
          | exact superpose b2e36 b2e349
          | exact resolve b2e349 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e349
        have b2e388 : ∀ X0 : G, (k (M.op (M.op (τ x) x) x) X0) = (M.op (M.op (M.op (τ x) x) x) X0) := by
          intro X0
          first
          | (have i₁ := b2e37 (τ x) x x
             have i₂ := b2e351
             grind)
          | exact superpose b2e351 b2e37
          | exact resolve b2e37 b2e351
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37 b2e351
        have b2e418 : ∀ X0 : G, (k (M.op (τ x) x) X0) = (M.op (M.op (τ x) x) X0) := by
          intro X0
          first
          | (have i₁ := b2e388 X0
             have i₂ := b2e30 (M.op (τ x) x)
             grind)
          | exact superpose b2e30 b2e388
          | exact resolve b2e388 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e388
        have b2e419 : ∀ X0 : G, (k (τ x) X0) = (M.op (τ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e418 X0
             have i₂ := b2e30 (τ x)
             grind)
          | exact superpose b2e30 b2e418
          | exact resolve b2e418 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e418
        have b2e490 : ∀ X0 : G, (k x (σ X0)) = (σ (M.op (τ x) X0)) := by
          intro X0
          first
          | (have i₁ := b2e23 x X0
             have i₂ := b2e419 X0
             grind)
          | exact superpose b2e419 b2e23
          | exact resolve b2e23 b2e419
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e419
        have b2e497 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op (τ x) X0)) := by
          intro X0
          first
          | (have i₁ := b2e490 X0
             have i₂ := b2e36 (σ X0)
             grind)
          | exact superpose b2e36 b2e490
          | exact resolve b2e490 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e490
        have b2e1054 : (M.op x (σ x)) = (σ (τ x)) := by
          first
          | (have i₁ := b2e497 x
             have i₂ := b2e30 (τ x)
             grind)
          | exact superpose b2e30 b2e497
          | exact resolve b2e497 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e497
        have b2e1075 : x = (M.op x (σ x)) := by
          first
          | (have i₁ := b2e1054
             have i₂ := b2e14 x
             grind)
          | exact superpose b2e14 b2e1054
          | exact resolve b2e1054 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1054
        have b2e1219 : ∀ X0 : G, (M.op X0 (M.op (σ x) x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e32 (σ x) X0
             have i₂ := b2e1075
             grind)
          | exact superpose b2e1075 b2e32
          | exact resolve b2e32 b2e1075
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e1075
        have b2e1238 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1219 X0
             have i₂ := b2e30 (σ x)
             grind)
          | exact superpose b2e30 b2e1219
          | exact resolve b2e1219 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30 b2e1219
        have b2e1416 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e1238 (σ x)
             grind)
          | exact superpose b2e1238 b2e21
          | (have r₁ := b2e21
             have r₂ := b2e1238 (σ x)
             grind)
          | exact resolve b2e21 b2e1238
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1238
        have b2e1424 : False := by grind
        exact b2e1424
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e27 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ x)) (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ x) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e27 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e27
          | exact resolve b3e27 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e32 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
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
        have b3e37 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e15 (σ x) X0
             have i₂ := b3e32 (σ x)
             grind)
          | exact superpose b3e32 b3e15
          | (have j0 := b3e15 (σ x) X0
             grind)
          | (have r₁ := b3e15 (σ x) x
             have r₂ := b3e32 (σ x)
             grind)
          | exact resolve b3e15 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e38 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b3e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e46 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) := by
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
        have b3e53 : x = (M.op x x) ∨ x = (k x y) := by grind
        clear b3e46
        have b3e54 : x = (k x y) := by
          first
          | (have r₁ := b3e53
             have r₂ := b3e20
             grind)
          | exact resolve b3e53 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e64 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 x X0
             have i₂ := b3e38 (σ X0)
             grind)
          | exact superpose b3e38 b3e18
          | exact resolve b3e18 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e843 : (σ x) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e64 y
             grind)
          | exact superpose b3e64 b3e23
          | exact resolve b3e23 b3e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e64
        have b3e867 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e843
             have i₂ := b3e54
             grind)
          | exact superpose b3e54 b3e843
          | exact resolve b3e843 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54 b3e843
        have b3e868 : False := by grind
        exact b3e868
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x y) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (σ x) ≠ (σ x) := by
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
          have b4e27 : False := by grind
          exact b4e27
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b5e28 : ∀ X0 : G, (M.op X0 (M.op (M.op y x) x)) = X0 := by
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
          have b5e30 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X0 (M.op X2 (M.op X0 X2))
               have i₂ := b5e13 X0 X2 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x (M.op y x)
               have i₂ := b5e28 x
               grind)
            | exact superpose b5e28 b5e13
            | exact resolve b5e13 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e95 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e30 y X0 x
               have i₂ := b5e32 y
               grind)
            | exact superpose b5e32 b5e30
            | exact resolve b5e30 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e32
          have b5e103 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e16 y X0
               have i₂ := b5e95 y
               grind)
            | exact superpose b5e95 b5e16
            | (have j0 := b5e16 y X0
               grind)
            | (have r₁ := b5e16 y x
               have r₂ := b5e95 y
               grind)
            | exact resolve b5e16 b5e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e105 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e17 X0 y
               have i₂ := b5e95 X0
               grind)
            | exact superpose b5e95 b5e17
            | (have j0 := b5e17 X0 y
               grind)
            | (have r₁ := b5e17 X0 y
               have r₂ := b5e95 X0
               grind)
            | exact resolve b5e17 b5e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e107 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op y X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 y
               have i₂ := b5e95 (M.op X0 (M.op y X0))
               grind)
            | exact superpose b5e95 b5e13
            | exact resolve b5e13 b5e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e108 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e105 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e105
          have b5e109 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b5e103 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103
          have b5e483 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 y) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X0 X1
               have i₂ := b5e108 X0
               grind)
            | exact superpose b5e108 b5e16
            | (have j0 := b5e16 X0 X1
               have j1 := b5e108 X0
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e108 X0
               grind)
            | exact resolve b5e16 b5e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e108
          have b5e500 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 y) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e483 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e483
          have b5e951 : ∀ X0 : G, (M.op X0 y) ≠ X0 ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e500 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e500
          have b5e952 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e951 X0
               grind)
            | (have r₁ := b5e951 X0
               have r₂ := b5e95 X0
               grind)
            | exact resolve b5e951 b5e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e951
          have b5e987 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e26 X0 y
               have i₂ := b5e952 (τ X0)
               grind)
            | exact superpose b5e952 b5e26
            | exact resolve b5e26 b5e952
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e952
          have b5e989 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e987 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e987
            | exact resolve b5e987 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e987
          have b5e1048 : y = (M.op y (σ y)) := by
            first
            | (have i₁ := b5e109 (σ y)
               have i₂ := b5e989 y
               grind)
            | exact superpose b5e989 b5e109
            | exact resolve b5e109 b5e989
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e109 b5e989
          have b5e1179 : ∀ X0 : G, (M.op X0 (M.op (σ y) y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e107 (σ y) X0
               have i₂ := b5e1048
               grind)
            | exact superpose b5e1048 b5e107
            | exact resolve b5e107 b5e1048
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e107 b5e1048
          have b5e1196 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1179 X0
               have i₂ := b5e95 (σ y)
               grind)
            | exact superpose b5e95 b5e1179
            | exact resolve b5e1179 b5e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95 b5e1179
          have b5e1460 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1196 (σ x)
               grind)
            | exact superpose b5e1196 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e1196 (σ x)
               grind)
            | exact resolve b5e24 b5e1196
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1196
          have b5e1465 : False := by grind
          exact b5e1465
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ x)) (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e29 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 := by
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
        have b6e30 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
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
        have b6e35 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e15 (σ x) X0
             have i₂ := b6e30 (σ x)
             grind)
          | exact superpose b6e30 b6e15
          | (have j0 := b6e15 (σ x) X0
             grind)
          | (have r₁ := b6e15 (σ x) x
             have r₂ := b6e30 (σ x)
             grind)
          | exact resolve b6e15 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e36 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b6e35 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e40 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e36 (σ X0)
             grind)
          | exact superpose b6e36 b6e18
          | exact resolve b6e18 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e374 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e30 (σ x)
             have i₂ := b6e40 x
             grind)
          | exact superpose b6e40 b6e30
          | exact resolve b6e30 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30 b6e40
        have b6e427 : (τ (σ x)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e374
             grind)
          | exact superpose b6e374 b6e13
          | exact resolve b6e13 b6e374
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e374
        have b6e429 : x = (k x x) := by
          first
          | (have i₁ := b6e427
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e427
          | exact resolve b6e427 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e427
        have b6e521 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e429
             grind)
          | exact superpose b6e429 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e429
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e429
        have b6e522 : x = (M.op x x) := by grind
        clear b6e521
        have b6e526 : False := by grind
        exact b6e526
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e34 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X0 (M.op X2 (M.op X0 X2))
               have i₂ := b7e13 X0 X2 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e87 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e34 (σ x) X0 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e34
            | exact resolve b7e34 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e365 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e34 (σ y) X0 (σ x)
               have i₂ := b7e87 (σ y)
               grind)
            | exact superpose b7e87 b7e34
            | exact resolve b7e34 b7e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e434 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e16 (σ y) X0
               have i₂ := b7e365 (σ y)
               grind)
            | exact superpose b7e365 b7e16
            | (have j0 := b7e16 (σ y) X0
               grind)
            | (have r₁ := b7e16 (σ y) x
               have r₂ := b7e365 (σ y)
               grind)
            | exact resolve b7e16 b7e365
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e451 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b7e434 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e434
          have b7e539 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 y X0
               have i₂ := b7e451 (σ X0)
               grind)
            | exact superpose b7e451 b7e19
            | exact resolve b7e19 b7e451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e451
          have b7e943 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e365 (σ y)
               have i₂ := b7e539 y
               grind)
            | exact superpose b7e539 b7e365
            | exact resolve b7e365 b7e539
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e365 b7e539
          have b7e1017 : (τ (σ y)) = (k y y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e943
               grind)
            | exact superpose b7e943 b7e14
            | exact resolve b7e14 b7e943
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e943
          have b7e1046 : y = (k y y) := by
            first
            | (have i₁ := b7e1017
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e1017
            | exact resolve b7e1017 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1017
          have b7e1109 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e1046
               grind)
            | exact superpose b7e1046 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e1046
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1046
          have b7e1110 : y = (M.op y y) := by grind
          clear b7e1109
          have b7e1251 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e34 y X0 y
               have i₂ := b7e1110
               grind)
            | exact superpose b7e1110 b7e34
            | exact resolve b7e34 b7e1110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e1261 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1251 X0
               have i₂ := b7e1110
               grind)
            | exact superpose b7e1110 b7e1251
            | exact resolve b7e1251 b7e1110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1251
          have b7e1269 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1261 X0
               have i₂ := b7e1110
               grind)
            | exact superpose b7e1110 b7e1261
            | exact resolve b7e1261 b7e1110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1110 b7e1261
          have b7e1438 : x ≠ x := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e1269 x
               grind)
            | exact superpose b7e1269 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e1269 x
               grind)
            | exact resolve b7e22 b7e1269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1269
          have b7e1439 : False := by grind
          exact b7e1439
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b8e32 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X0 (M.op X2 (M.op X0 X2))
               have i₂ := b8e13 X0 X2 X0
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          have b8e52 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e17 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e17
            | (have j0 := b8e17 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
               grind)
            | (have r₁ := b8e17 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
               have r₂ := b8e13 X0 X1 X2
               grind)
            | exact resolve b8e17 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e52 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e52
          have b8e67 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e18 (σ X1) (σ X0)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X1) (σ X1)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e73 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X2
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X1
               have j1 := b8e18 X0 X2
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e76 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e73 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e91 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 X0 X1 X0
               have i₂ := b8e18 X0 X2
               grind)
            | exact superpose b8e18 b8e32
            | (have j1 := b8e18 X0 X2
               grind)
            | exact resolve b8e32 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e211 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 (M.op (M.op X2 (M.op X3 X2)) X3)) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e53 X0 X2 X3
               grind)
            | exact superpose b8e53 b8e16
            | (have j0 := b8e16 X0 X1
               have j1 := b8e53 X0 X2 X3
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e53 X0 X1 X2
               grind)
            | exact resolve b8e16 b8e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e218 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 (M.op (M.op X2 (M.op X3 X2)) X3)) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b8e211 X0 X1 X2 X3
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e211
          have b8e389 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e76 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e666 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X0) (M.op (σ X2) (σ X0)))) = X1 ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 (σ X0) X1 (σ X2)
               have i₂ := b8e67 X2 X0
               grind)
            | exact superpose b8e67 b8e32
            | (have j1 := b8e67 X2 X0
               grind)
            | exact resolve b8e32 b8e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e673 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e67 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e674 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e673 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e673
          have b8e925 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) ≠ X0 ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e218 X0 X1 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e218
          have b8e930 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e925 X0 X1 X2
               grind)
            | (have r₁ := b8e925 X0 X1 X2
               have r₂ := b8e13 X0 X1 X2
               grind)
            | exact resolve b8e925 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e925
          have b8e949 : ∀ X0 X1 X2 : G, (k X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e930 X1 X0 (M.op X2 (M.op X0 X2))
               have i₂ := b8e13 X0 X2 X0
               grind)
            | exact superpose b8e13 b8e930
            | exact resolve b8e930 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e930
          have b8e1075 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ≠ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ∨ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
            intro X0 X1
            first
            | (have i₁ := b8e674 (M.op X0 (M.op X1 (M.op X0 X1)))
               have i₂ := b8e949 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
               grind)
            | exact superpose b8e949 b8e674
            | (have j0 := b8e674 (M.op X0 (M.op X1 (M.op X0 X1)))
               grind)
            | exact resolve b8e674 b8e949
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e674 b8e949
          have b8e1087 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
            intro X0 X1
            first
            | (have j0 := b8e1075 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1075
          have b8e3792 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b8e389 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e389
          have b8e3795 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e3792 X0
               have j1 := b8e16 X0 X0
               grind)
            | (have r₁ := b8e3792 X0
               have r₂ := b8e16 X0 x
               grind)
            | exact resolve b8e3792 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3792
          have b8e3841 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e3795 (σ X0)
               grind)
            | exact superpose b8e3795 b8e19
            | exact resolve b8e19 b8e3795
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3845 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e44 X0 X0
               have i₂ := b8e3795 (τ X0)
               grind)
            | exact superpose b8e3795 b8e44
            | exact resolve b8e44 b8e3795
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44
          have b8e3852 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e3845 X0
               have i₂ := b8e3795 X0
               grind)
            | exact superpose b8e3795 b8e3845
            | exact resolve b8e3845 b8e3795
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3845
          have b8e3856 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e3841 X0
               have i₂ := b8e3795 X0
               grind)
            | exact superpose b8e3795 b8e3841
            | exact resolve b8e3841 b8e3795
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3795 b8e3841
          have b8e4214 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (σ X0) (σ X0)
               have i₂ := b8e3856 X0
               grind)
            | exact superpose b8e3856 b8e13
            | exact resolve b8e13 b8e3856
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e8084 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e4214 (M.op X0 (M.op X1 (M.op X0 X1))) X2
               have i₂ := b8e32 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
               grind)
            | exact superpose b8e32 b8e4214
            | exact resolve b8e4214 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4214
          have b8e8349 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e8084 X0 X1 X2
               have i₂ := b8e1087 X0 X1
               grind)
            | exact superpose b8e1087 b8e8084
            | exact resolve b8e8084 b8e1087
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8084
          have b8e8377 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e8349 X0 X1 X2
               have i₂ := b8e1087 X0 X1
               grind)
            | exact superpose b8e1087 b8e8349
            | exact resolve b8e8349 b8e1087
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1087 b8e8349
          have b8e8637 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (M.op X1 (σ X0)) = X1 ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e8377 X0 X0 X1
               have i₂ := b8e91 X0 X0 X2
               grind)
            | exact superpose b8e91 b8e8377
            | (have j1 := b8e91 X0 X1 X2
               grind)
            | exact resolve b8e8377 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91 b8e8377
          have b8e64755 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 (σ X0) X1 (σ X2)
               have i₂ := b8e666 X2 (σ X0) X0
               grind)
            | exact superpose b8e666 b8e32
            | (have j1 := b8e666 X2 X1 X0
               grind)
            | exact resolve b8e32 b8e666
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e666
          have b8e65600 : ∀ X0 X1 X2 : G, (σ X2) = (σ (M.op X2 X2)) ∨ (M.op X1 (σ X0)) = X1 ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e64755 X0 X1 X2
               have i₂ := b8e3856 X2
               grind)
            | exact superpose b8e3856 b8e64755
            | (have j0 := b8e64755 X0 X1 X2
               grind)
            | exact resolve b8e64755 b8e3856
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3856 b8e64755
          have b8e102147 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e65600 x (σ x) X0
               grind)
            | exact superpose b8e65600 b8e23
            | (have j1 := b8e65600 x x X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e65600 x (σ x) x
               grind)
            | exact resolve b8e23 b8e65600
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65600
          have b8e102153 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
            intro X0
            first
            | (have j0 := b8e102147 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102147
          have b8e102732 : ∀ X0 : G, (σ (τ X0)) = (σ (τ (M.op X0 X0))) ∨ (M.op (σ x) (σ (τ X0))) = (σ (k (τ X0) x)) := by
            intro X0
            first
            | (have i₁ := b8e102153 (τ X0)
               have i₂ := b8e3852 X0
               grind)
            | exact superpose b8e3852 b8e102153
            | (have j0 := b8e102153 (τ X0)
               grind)
            | exact resolve b8e102153 b8e3852
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3852 b8e102153
          have b8e102778 : ∀ X0 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (M.op (σ x) (σ (τ X0))) = (σ (k (τ X0) x)) := by
            intro X0
            first
            | (have i₁ := b8e102732 X0
               have i₂ := b8e15 (M.op X0 X0)
               grind)
            | exact superpose b8e15 b8e102732
            | (have j0 := b8e102732 X0
               grind)
            | exact resolve b8e102732 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102732
          have b8e102781 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ x) (σ (τ X0))) = (σ (k (τ X0) x)) := by
            intro X0
            first
            | (have i₁ := b8e102778 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e102778
            | (have j0 := b8e102778 X0
               grind)
            | exact resolve b8e102778 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102778
          have b8e102782 : ∀ X0 : G, (M.op (σ x) (σ (τ X0))) = (k X0 (σ x)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e102781 X0
               have i₂ := b8e25 X0 x
               grind)
            | exact superpose b8e25 b8e102781
            | (have j0 := b8e102781 X0
               grind)
            | exact resolve b8e102781 b8e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25 b8e102781
          have b8e102783 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e102782 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e102782
            | (have j0 := b8e102782 X0
               grind)
            | exact resolve b8e102782 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102782
          have b8e102838 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X0 X1 X0
               have i₂ := b8e102783 X0
               grind)
            | exact superpose b8e102783 b8e32
            | (have j1 := b8e102783 X0
               grind)
            | exact resolve b8e32 b8e102783
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102783
          have b8e113457 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X0 X1 X0
               have i₂ := b8e102838 X0 X0
               grind)
            | exact superpose b8e102838 b8e32
            | (have j1 := b8e102838 X0 X1
               grind)
            | exact resolve b8e32 b8e102838
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102838
          have b8e113649 : ∀ X0 X1 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (M.op X1 (σ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 x
               have i₂ := b8e113457 (σ X0) X1
               grind)
            | exact superpose b8e113457 b8e19
            | (have j1 := b8e113457 (σ X0) X1
               grind)
            | exact resolve b8e19 b8e113457
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113457
          have b8e114990 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b8e20
               have i₂ := b8e113649 y X0
               grind)
            | exact superpose b8e113649 b8e20
            | (have j1 := b8e113649 y X0
               grind)
            | exact resolve b8e20 b8e113649
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113649
          have b8e116723 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k y X0) = (M.op X0 y) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e8637 y (σ x) X0
               grind)
            | exact superpose b8e8637 b8e24
            | (have j1 := b8e8637 y x X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e8637 y (σ x) x
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e8637 (σ x) x (σ y)
               grind)
            | exact resolve b8e24 b8e8637
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8637
          have b8e116726 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b8e116723 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e116723
          have b8e116736 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b8e114990 X0
               have i₂ := b8e116726 x
               grind)
            | exact superpose b8e116726 b8e114990
            | (have j0 := b8e114990 X0
               have j1 := b8e116726 x
               grind)
            | exact resolve b8e114990 b8e116726
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e114990 b8e116726
          have b8e116761 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op y x) := by
            intro X0
            first
            | (have j0 := b8e116736 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e116736
          have b8e117956 : (σ x) ≠ (σ x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e116761 (σ x)
               grind)
            | exact superpose b8e116761 b8e24
            | (have r₁ := b8e24
               have r₂ := b8e116761 (σ x)
               grind)
            | exact resolve b8e24 b8e116761
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e116761
          have b8e118006 : y = (M.op y x) := by grind
          clear b8e117956
          have b8e118031 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = X0 := by
            intro X0
            first
            | (have i₁ := b8e32 y X0 x
               have i₂ := b8e118006
               grind)
            | exact superpose b8e118006 b8e32
            | exact resolve b8e32 b8e118006
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e118006
          have b8e119164 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b8e32 x X0 y
               have i₂ := b8e118031 x
               grind)
            | exact superpose b8e118031 b8e32
            | exact resolve b8e32 b8e118031
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32 b8e118031
          have b8e120878 : x ≠ x := by
            first
            | (have i₁ := b8e21
               have i₂ := b8e119164 x
               grind)
            | exact superpose b8e119164 b8e21
            | (have r₁ := b8e21
               have r₂ := b8e119164 x
               grind)
            | exact resolve b8e21 b8e119164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e119164
          have b8e120879 : False := by grind
          exact b8e120879

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_Equation1061 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x x) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) x)) = X0 := by
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
      have b0e33 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
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
      have b0e35 : ∀ X0 : G, (M.op X0 x) = X0 := by
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
      have b0e39 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
      have b0e41 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b0e14 x X0
           have i₂ := b0e35 x
           grind)
        | exact superpose b0e35 b0e14
        | (have j0 := b0e14 x X0
           grind)
        | (have r₁ := b0e14 x x
           have r₂ := b0e35 x
           grind)
        | exact resolve b0e14 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e42 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
        intro X0
        first
        | (have j0 := b0e41 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e44 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b0e39 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e99 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 x X0
           have i₂ := b0e44 (σ X0)
           grind)
        | exact superpose b0e44 b0e17
        | exact resolve b0e17 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e103 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e99 X0
           have i₂ := b0e42 X0
           grind)
        | exact superpose b0e42 b0e99
        | exact resolve b0e99 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e99
      have b0e1886 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e103 y
           grind)
        | exact superpose b0e103 b0e18
        | (have r₁ := b0e18
           have r₂ := b0e103 y
           grind)
        | exact resolve b0e18 b0e103
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e103
      have b0e1912 : False := by grind
      exact b0e1912
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e25 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) x)) = X0 := by
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
        have b1e31 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
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
        have b1e33 : ∀ X0 : G, (M.op X0 x) = X0 := by
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
        have b1e39 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b1e15 x X0
             have i₂ := b1e33 x
             grind)
          | exact superpose b1e33 b1e15
          | (have j0 := b1e15 x X0
             grind)
          | (have r₁ := b1e15 x x
             have r₂ := b1e33 x
             grind)
          | exact resolve b1e15 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b1e39 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e52 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (M.op X0 x) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 x
             have i₂ := b1e33 x
             grind)
          | exact superpose b1e33 b1e16
          | (have j0 := b1e16 X0 x
             grind)
          | (have r₁ := b1e16 X0 x
             have r₂ := b1e33 x
             grind)
          | exact resolve b1e16 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 x) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e52 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e60 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e55 X0
             have j1 := b1e15 X0 x
             grind)
          | (have r₁ := b1e55 X0
             have r₂ := b1e15 X0 x
             grind)
          | exact resolve b1e55 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e65 : ∀ X0 : G, (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b1e60 X0
             have i₂ := b1e33 X0
             grind)
          | exact superpose b1e33 b1e60
          | exact resolve b1e60 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e108 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e23 X0 x
             have i₂ := b1e65 (τ X0)
             grind)
          | exact superpose b1e65 b1e23
          | exact resolve b1e23 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e65
        have b1e115 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e108 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e108
          | exact resolve b1e108 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e108
        have b1e124 : x = (M.op x (σ x)) := by
          first
          | (have i₁ := b1e40 (σ x)
             have i₂ := b1e115 x
             grind)
          | exact superpose b1e115 b1e40
          | exact resolve b1e40 b1e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40 b1e115
        have b1e141 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) x) x)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ x) x
             have i₂ := b1e124
             grind)
          | exact superpose b1e124 b1e12
          | exact resolve b1e12 b1e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e124
        have b1e142 : ∀ X0 : G, (M.op X0 (M.op (σ x) x)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e141 X0
             have i₂ := b1e33 (M.op (σ x) x)
             grind)
          | exact superpose b1e33 b1e141
          | exact resolve b1e141 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e141
        have b1e143 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e142 X0
             have i₂ := b1e33 (σ x)
             grind)
          | exact superpose b1e33 b1e142
          | exact resolve b1e142 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e142
        have b1e171 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e143 (σ x)
             grind)
          | exact superpose b1e143 b1e21
          | (have r₁ := b1e21
             have r₂ := b1e143 (σ x)
             grind)
          | exact resolve b1e21 b1e143
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e143
        have b1e172 : False := by grind
        exact b1e172
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e25 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e25 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e25
          | exact resolve b2e25 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e30 : ∀ X0 : G, (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e29 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e29
          | exact resolve b2e29 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e35 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b2e15 x X0
             have i₂ := b2e30 x
             grind)
          | exact superpose b2e30 b2e15
          | (have j0 := b2e15 x X0
             grind)
          | (have r₁ := b2e15 x x
             have r₂ := b2e30 x
             grind)
          | exact resolve b2e15 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b2e35 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e41 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (M.op X0 x) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b2e16 X0 x
             have i₂ := b2e30 x
             grind)
          | exact superpose b2e30 b2e16
          | (have j0 := b2e16 X0 x
             grind)
          | (have r₁ := b2e16 X0 x
             have r₂ := b2e30 x
             grind)
          | exact resolve b2e16 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e42 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 x) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b2e41 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e45 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b2e42 X0
             have j1 := b2e15 X0 x
             grind)
          | (have r₁ := b2e42 X0
             have r₂ := b2e15 X0 x
             grind)
          | exact resolve b2e42 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42
        have b2e48 : ∀ X0 : G, (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e45 X0
             have i₂ := b2e30 X0
             grind)
          | exact superpose b2e30 b2e45
          | exact resolve b2e45 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45
        have b2e103 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e23 X0 x
             have i₂ := b2e48 (τ X0)
             grind)
          | exact superpose b2e48 b2e23
          | exact resolve b2e23 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e48
        have b2e108 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e103 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e103
          | exact resolve b2e103 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e103
        have b2e115 : x = (M.op x (σ x)) := by
          first
          | (have i₁ := b2e36 (σ x)
             have i₂ := b2e108 x
             grind)
          | exact superpose b2e108 b2e36
          | exact resolve b2e36 b2e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e108
        have b2e130 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) x) x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 (σ x) x
             have i₂ := b2e115
             grind)
          | exact superpose b2e115 b2e12
          | exact resolve b2e12 b2e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e115
        have b2e131 : ∀ X0 : G, (M.op X0 (M.op (σ x) x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e130 X0
             have i₂ := b2e30 (M.op (σ x) x)
             grind)
          | exact superpose b2e30 b2e130
          | exact resolve b2e130 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e130
        have b2e133 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e131 X0
             have i₂ := b2e30 (σ x)
             grind)
          | exact superpose b2e30 b2e131
          | exact resolve b2e131 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30 b2e131
        have b2e166 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e133 (σ x)
             grind)
          | exact superpose b2e133 b2e21
          | (have r₁ := b2e21
             have r₂ := b2e133 (σ x)
             grind)
          | exact resolve b2e21 b2e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e133
        have b2e168 : False := by grind
        exact b2e168
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : y = (M.op y y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 (τ X0) X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e18
          | exact resolve b3e18 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e25 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e25
          | exact resolve b3e25 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e33 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e31 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e31
          | exact resolve b3e31 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e39 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b3e15 y X0
             have i₂ := b3e33 y
             grind)
          | exact superpose b3e33 b3e15
          | (have j0 := b3e15 y X0
             grind)
          | (have r₁ := b3e15 y x
             have r₂ := b3e33 y
             grind)
          | exact resolve b3e15 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e40 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
          intro X0
          first
          | (have j0 := b3e39 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e51 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e33 y
             grind)
          | exact superpose b3e33 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | (have r₁ := b3e16 X0 y
             have r₂ := b3e33 y
             grind)
          | exact resolve b3e16 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e54 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e51 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e59 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e54 X0
             have j1 := b3e15 X0 y
             grind)
          | (have r₁ := b3e54 X0
             have r₂ := b3e15 X0 x
             grind)
          | exact resolve b3e54 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e64 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e59 X0
             have i₂ := b3e33 X0
             grind)
          | exact superpose b3e33 b3e59
          | exact resolve b3e59 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
        have b3e103 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e23 X0 y
             have i₂ := b3e64 (τ X0)
             grind)
          | exact superpose b3e64 b3e23
          | exact resolve b3e23 b3e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e64
        have b3e110 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e103 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e103
          | exact resolve b3e103 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e103
        have b3e119 : y = (M.op y (σ y)) := by
          first
          | (have i₁ := b3e40 (σ y)
             have i₂ := b3e110 y
             grind)
          | exact superpose b3e110 b3e40
          | exact resolve b3e40 b3e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40 b3e110
        have b3e134 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) y) y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ y) y
             have i₂ := b3e119
             grind)
          | exact superpose b3e119 b3e12
          | exact resolve b3e12 b3e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e119
        have b3e135 : ∀ X0 : G, (M.op X0 (M.op (σ y) y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e134 X0
             have i₂ := b3e33 (M.op (σ y) y)
             grind)
          | exact superpose b3e33 b3e134
          | exact resolve b3e134 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e134
        have b3e136 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e135 X0
             have i₂ := b3e33 (σ y)
             grind)
          | exact superpose b3e33 b3e135
          | exact resolve b3e135 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e135
        have b3e164 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e136 (σ x)
             grind)
          | exact superpose b3e136 b3e19
          | exact resolve b3e19 b3e136
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e136
        have b3e167 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e164
             have i₂ := b3e33 x
             grind)
          | exact superpose b3e33 b3e164
          | exact resolve b3e164 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e164
        have b3e168 : False := by grind
        exact b3e168
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e31 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e32 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e32
            | exact resolve b4e32 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e37 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
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
          have b4e38 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e36 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e36
            | exact resolve b4e36 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e39 : ∀ X0 : G, (M.op X0 y) = X0 := by
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
          have b4e53 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e38 (σ x)
               grind)
            | exact superpose b4e38 b4e20
            | exact resolve b4e20 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e55 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e53
               have i₂ := b4e39 x
               grind)
            | exact superpose b4e39 b4e53
            | exact resolve b4e53 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e53
          have b4e56 : False := by grind
          exact b4e56
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e31 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e31 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e31
            | exact resolve b5e31 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e36 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e35 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e35
            | exact resolve b5e35 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e41 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b5e16 y X0
               have i₂ := b5e36 y
               grind)
            | exact superpose b5e36 b5e16
            | (have j0 := b5e16 y X0
               grind)
            | (have r₁ := b5e16 y x
               have r₂ := b5e36 y
               grind)
            | exact resolve b5e16 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
            intro X0
            first
            | (have j0 := b5e41 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e47 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b5e17 X0 y
               have i₂ := b5e36 y
               grind)
            | exact superpose b5e36 b5e17
            | (have j0 := b5e17 X0 y
               grind)
            | (have r₁ := b5e17 X0 y
               have r₂ := b5e36 y
               grind)
            | exact resolve b5e17 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b5e47 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e51 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b5e48 X0
               have j1 := b5e16 X0 y
               grind)
            | (have r₁ := b5e48 X0
               have r₂ := b5e16 X0 x
               grind)
            | exact resolve b5e48 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e54 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e51 X0
               have i₂ := b5e36 X0
               grind)
            | exact superpose b5e36 b5e51
            | exact resolve b5e51 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e58 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e25 X0 y
               have i₂ := b5e54 (τ X0)
               grind)
            | exact superpose b5e54 b5e25
            | exact resolve b5e25 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e54
          have b5e60 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e58 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e58
            | exact resolve b5e58 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e95 : y = (M.op y (σ y)) := by
            first
            | (have i₁ := b5e42 (σ y)
               have i₂ := b5e60 y
               grind)
            | exact superpose b5e60 b5e42
            | exact resolve b5e42 b5e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e60
          have b5e107 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) y) y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 (σ y) y
               have i₂ := b5e95
               grind)
            | exact superpose b5e95 b5e13
            | exact resolve b5e13 b5e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95
          have b5e108 : ∀ X0 : G, (M.op X0 (M.op (σ y) y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e107 X0
               have i₂ := b5e36 (M.op (σ y) y)
               grind)
            | exact superpose b5e36 b5e107
            | exact resolve b5e107 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e107
          have b5e109 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e108 X0
               have i₂ := b5e36 (σ y)
               grind)
            | exact superpose b5e36 b5e108
            | exact resolve b5e108 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e108
          have b5e136 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e109 (σ y)
               grind)
            | exact superpose b5e109 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e109 (σ y)
               grind)
            | exact resolve b5e24 b5e109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e109
          have b5e137 : False := by grind
          exact b5e137
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ x)) (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e29 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 := by
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
        have b6e30 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
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
        have b6e35 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e15 (σ x) X0
             have i₂ := b6e30 (σ x)
             grind)
          | exact superpose b6e30 b6e15
          | (have j0 := b6e15 (σ x) X0
             grind)
          | (have r₁ := b6e15 (σ x) x
             have r₂ := b6e30 (σ x)
             grind)
          | exact resolve b6e15 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e36 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b6e35 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e43 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e16 X0 (σ x)
             have i₂ := b6e30 (σ x)
             grind)
          | exact superpose b6e30 b6e16
          | (have j0 := b6e16 X0 (σ x)
             grind)
          | (have r₁ := b6e16 X0 (σ x)
             have r₂ := b6e30 (σ x)
             grind)
          | exact resolve b6e16 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e44 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b6e43 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e47 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b6e44 X0
             have j1 := b6e15 X0 (σ x)
             grind)
          | (have r₁ := b6e44 X0
             have r₂ := b6e15 X0 x
             grind)
          | exact resolve b6e44 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e50 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e47 X0
             have i₂ := b6e30 X0
             grind)
          | exact superpose b6e30 b6e47
          | exact resolve b6e47 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47
        have b6e55 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 x
             have i₂ := b6e50 (σ X0)
             grind)
          | exact superpose b6e50 b6e18
          | exact resolve b6e18 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e79 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b6e13 (k X0 x)
             have i₂ := b6e55 X0
             grind)
          | exact superpose b6e55 b6e13
          | exact resolve b6e13 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e80 : ∀ X0 : G, (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b6e79 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e79
          | exact resolve b6e79 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e97 : (σ x) = (M.op (σ x) x) := by
          first
          | (have i₁ := b6e36 x
             have i₂ := b6e80 (σ x)
             grind)
          | exact superpose b6e80 b6e36
          | exact resolve b6e36 b6e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36 b6e80
        have b6e141 : ∀ X0 : G, (M.op X0 (M.op (M.op x (σ x)) (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 x (σ x)
             have i₂ := b6e97
             grind)
          | exact superpose b6e97 b6e12
          | exact resolve b6e12 b6e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e97
        have b6e142 : ∀ X0 : G, (M.op X0 (M.op x (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e141 X0
             have i₂ := b6e30 (M.op x (σ x))
             grind)
          | exact superpose b6e30 b6e141
          | exact resolve b6e141 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e141
        have b6e144 : ∀ X0 : G, (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b6e142 X0
             have i₂ := b6e30 x
             grind)
          | exact superpose b6e30 b6e142
          | exact resolve b6e142 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30 b6e142
        have b6e173 : x ≠ x := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e144 x
             grind)
          | exact superpose b6e144 b6e20
          | (have r₁ := b6e20
             have r₂ := b6e144 x
             grind)
          | exact resolve b6e20 b6e144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e144
        have b6e174 : False := by grind
        exact b6e174
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e31 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
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
          have b7e36 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
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
          have b7e42 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e16 (σ y) X0
               have i₂ := b7e36 (σ y)
               grind)
            | exact superpose b7e36 b7e16
            | (have j0 := b7e16 (σ y) X0
               grind)
            | (have r₁ := b7e16 (σ y) x
               have r₂ := b7e36 (σ y)
               grind)
            | exact resolve b7e16 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e43 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) := by
            intro X0
            first
            | (have j0 := b7e42 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e48 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e17 X0 (σ y)
               have i₂ := b7e36 (σ y)
               grind)
            | exact superpose b7e36 b7e17
            | (have j0 := b7e17 X0 (σ y)
               grind)
            | (have r₁ := b7e17 X0 (σ y)
               have r₂ := b7e36 (σ y)
               grind)
            | exact resolve b7e17 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e49 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b7e48 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e52 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b7e49 X0
               have j1 := b7e16 X0 (σ y)
               grind)
            | (have r₁ := b7e49 X0
               have r₂ := b7e16 X0 x
               grind)
            | exact resolve b7e49 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e55 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e52 X0
               have i₂ := b7e36 X0
               grind)
            | exact superpose b7e36 b7e52
            | exact resolve b7e52 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e59 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 y
               have i₂ := b7e55 (σ X0)
               grind)
            | exact superpose b7e55 b7e19
            | exact resolve b7e19 b7e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e88 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b7e14 (k X0 y)
               have i₂ := b7e59 X0
               grind)
            | exact superpose b7e59 b7e14
            | exact resolve b7e14 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e89 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b7e88 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e88
            | exact resolve b7e88 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e181 : (σ y) = (M.op (σ y) y) := by
            first
            | (have i₁ := b7e89 (σ y)
               have i₂ := b7e43 y
               grind)
            | exact superpose b7e43 b7e89
            | exact resolve b7e89 b7e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43 b7e89
          have b7e204 : ∀ X0 : G, (M.op X0 (M.op (M.op y (σ y)) (σ y))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 y (σ y)
               have i₂ := b7e181
               grind)
            | exact superpose b7e181 b7e13
            | exact resolve b7e13 b7e181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e181
          have b7e205 : ∀ X0 : G, (M.op X0 (M.op y (σ y))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e204 X0
               have i₂ := b7e36 (M.op y (σ y))
               grind)
            | exact superpose b7e36 b7e204
            | exact resolve b7e204 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e204
          have b7e208 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b7e205 X0
               have i₂ := b7e36 y
               grind)
            | exact superpose b7e36 b7e205
            | exact resolve b7e205 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36 b7e205
          have b7e280 : y ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e208 y
               grind)
            | exact superpose b7e208 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e208 y
               grind)
            | exact resolve b7e22 b7e208
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e208
          have b7e281 : False := by grind
          exact b7e281
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e77 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ x)
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) x
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 X0 (σ x)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e85 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b8e77 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77
          have b8e169 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 x
               have i₂ := b8e85 (σ X0)
               grind)
            | exact superpose b8e85 b8e19
            | (have j1 := b8e85 (σ X0)
               grind)
            | exact resolve b8e19 b8e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85
          have b8e10526 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e169 y
               grind)
            | exact superpose b8e169 b8e24
            | (have j1 := b8e169 y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e169 y
               grind)
            | exact resolve b8e24 b8e169
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e169
          have b8e10586 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
          clear b8e10526
          have b8e10716 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e10586
               grind)
            | exact superpose b8e10586 b8e20
            | exact resolve b8e20 b8e10586
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10586
          have b8e10908 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e10716
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e10716
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e10716 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10716
          have b8e10921 : y = (M.op y y) ∨ x = (M.op x x) := by grind
          clear b8e10908
          have b8e10926 : x = (M.op x x) := by
            first
            | (have r₁ := b8e10921
               have r₂ := b8e22
               grind)
            | exact resolve b8e10921 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10921
          have b8e10927 : False := by grind
          exact b8e10927

/-- `Equation1096`: `x = y ◇ ((x ◇ (z ◇ y)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then X else if m(Y,Y) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_x_x_x_pyx_Equation1096 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1096 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1096.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X1)) X0)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e35 : ∀ X0 : G, (M.op y (M.op (M.op X0 x) X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) (M.op (M.op X3 X0) X3)) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X3 (M.op (M.op X0 (M.op X1 X2)) X0) X2
             have i₂ := b1e12 X0 X2 X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 X0 (M.op X0 (M.op x X1))
             have i₂ := b1e12 X0 X1 x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : y = (M.op x x) := by
          first
          | (have i₁ := b1e38 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e38
          | exact resolve b1e38 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e38 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e38
          | exact resolve b1e38 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X1)) X0) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e38 X1 (M.op (M.op X0 (M.op X2 X1)) X0)
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e38
          | exact resolve b1e38 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b1e53 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e38 X1 X1
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e38 X0 X1
             have i₂ := b1e17 (M.op X0 X1) X1
             grind)
          | exact superpose b1e17 b1e38
          | (have j1 := b1e17 X0 X1
             grind)
          | exact resolve b1e38 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e63 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e64 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e63 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63
        have b1e65 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e64 X0 X1
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e64 X0 X1
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e64 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64
        have b1e73 : ∀ X0 : G, (M.op (M.op X0 x) X0) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e38 y (M.op (M.op X0 x) X0)
             have i₂ := b1e35 X0
             grind)
          | exact superpose b1e35 b1e38
          | exact resolve b1e38 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e99 : ∀ X0 : G, (M.op (M.op X0 x) (M.op y X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e38 (M.op X0 x) X0
             have i₂ := b1e73 X0
             grind)
          | exact superpose b1e73 b1e38
          | exact resolve b1e38 b1e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e65 (σ X0) (σ X1)
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e65
          | exact resolve b1e65 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e126 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op y X0) x) X0) := by
          intro X0
          first
          | (have i₁ := b1e99 (M.op y X0)
             have i₂ := b1e38 y X0
             grind)
          | exact superpose b1e38 b1e99
          | exact resolve b1e99 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e99
        have b1e167 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X1 X0)) (M.op X0 X1)) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e37 (M.op X1 X0) X2 X3 X1
             have i₂ := b1e38 X1 X0
             grind)
          | exact superpose b1e38 b1e37
          | exact resolve b1e37 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e206 : ∀ X0 X1 X3 : G, (M.op (M.op X3 (M.op X1 X0)) (M.op X0 X1)) = X1 := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e167 X0 X1 x X3
             have i₂ := b1e42 (M.op X1 X0) X3 x
             grind)
          | exact superpose b1e42 b1e167
          | exact resolve b1e167 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42 b1e167
        have b1e407 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e50 y y
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e50
          | exact resolve b1e50 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e458 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b1e407
        have b1e1491 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X0) = X2 ∨ (M.op X2 X0) = (k X0 X2) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e206 X1 X1 x
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e206 X0 X1 x
             have i₂ := b1e17 (M.op X0 X1) X1
             grind)
          | exact superpose b1e17 b1e206
          | (have j1 := b1e17 X0 X2
             grind)
          | exact resolve b1e206 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e206
        have b1e3505 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k y y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e113 y y
             grind)
          | exact superpose b1e113 b1e22
          | (have j1 := b1e113 y y
             grind)
          | exact resolve b1e22 b1e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e3525 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e38 (σ X1) (σ X0)
             have i₂ := b1e113 X0 X1
             grind)
          | exact superpose b1e113 b1e38
          | (have j1 := b1e113 X0 X1
             grind)
          | exact resolve b1e38 b1e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e113
        have b1e18497 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y y)) := by grind
        clear b1e3505
        have b1e18505 : (σ x) = (σ (k y y)) := by
          first
          | (have r₁ := b1e18497
             have r₂ := b1e458
             grind)
          | exact resolve b1e18497 b1e458
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e458 b1e18497
        have b1e19591 : (k y y) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e18505
             grind)
          | exact superpose b1e18505 b1e13
          | exact resolve b1e13 b1e18505
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e19593 : ∀ X0 : G, (σ (k X0 (k y y))) = (k (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 (k y y)
             have i₂ := b1e18505
             grind)
          | exact superpose b1e18505 b1e18
          | exact resolve b1e18 b1e18505
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18505
        have b1e19691 : ∀ X0 : G, (σ (k X0 x)) = (σ (k X0 (k y y))) := by
          intro X0
          first
          | (have i₁ := b1e19593 X0
             have i₂ := b1e18 X0 x
             grind)
          | exact superpose b1e18 b1e19593
          | exact resolve b1e19593 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19593
        have b1e19693 : x = (k y y) := by
          first
          | (have i₁ := b1e19591
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e19591
          | exact resolve b1e19591 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19591
        have b1e20051 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e53 y y
             have i₂ := b1e19693
             grind)
          | exact superpose b1e19693 b1e53
          | (have j0 := b1e53 y y
             grind)
          | exact resolve b1e53 b1e19693
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e20052 : x = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b1e65 y y
             have i₂ := b1e19693
             grind)
          | exact superpose b1e19693 b1e65
          | exact resolve b1e65 b1e19693
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e20062 : y = (M.op y y) ∨ x = (M.op y y) := by grind
        clear b1e20051
        have b1e22418 : x ≠ y ∨ x = (M.op y y) := by grind
        clear b1e20062
        have b1e22427 : x = (M.op y y) := by
          first
          | (have r₁ := b1e22418
             have r₂ := b1e20052
             grind)
          | exact resolve b1e22418 b1e20052
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e20052 b1e22418
        have b1e23867 : y = (M.op y x) := by
          first
          | (have i₁ := b1e38 y y
             have i₂ := b1e22427
             grind)
          | exact superpose b1e22427 b1e38
          | exact resolve b1e38 b1e22427
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38 b1e22427
        have b1e57843 : ∀ X0 : G, (M.op y x) = X0 ∨ (M.op X0 x) = (k x X0) ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e126 x
             have i₂ := b1e1491 x (M.op y x) X0
             grind)
          | (have i₁ := b1e126 X0
             have i₂ := b1e1491 X0 x (M.op (M.op (M.op y X0) x) X0)
             grind)
          | exact superpose b1e1491 b1e126
          | (have j1 := b1e1491 x x X0
             grind)
          | exact resolve b1e126 b1e1491
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e126 b1e1491
        have b1e58054 : ∀ X0 : G, (M.op X0 x) = (k x X0) ∨ y = X0 ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e57843 X0
             have i₂ := b1e23867
             grind)
          | exact superpose b1e23867 b1e57843
          | (have j0 := b1e57843 X0
             grind)
          | exact resolve b1e57843 b1e23867
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23867 b1e57843
        have b1e61358 : (σ (k x x)) = (σ (M.op (k y y) x)) ∨ y = (k y y) ∨ x = (M.op x (k y y)) := by
          first
          | (have i₁ := b1e19691 x
             have i₂ := b1e58054 (k y y)
             grind)
          | exact superpose b1e58054 b1e19691
          | (have j1 := b1e58054 (k y y)
             grind)
          | exact resolve b1e19691 b1e58054
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19691 b1e58054
        have b1e61373 : (σ (k x x)) = (σ (M.op x x)) ∨ y = (k y y) ∨ x = (M.op x (k y y)) := by
          first
          | (have i₁ := b1e61358
             have i₂ := b1e19693
             grind)
          | exact superpose b1e19693 b1e61358
          | exact resolve b1e61358 b1e19693
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61358
        have b1e61395 : (σ y) = (σ (k x x)) ∨ y = (k y y) ∨ x = (M.op x (k y y)) := by
          first
          | (have i₁ := b1e61373
             have i₂ := b1e40
             grind)
          | exact superpose b1e40 b1e61373
          | exact resolve b1e61373 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61373
        have b1e61406 : x = y ∨ (σ y) = (σ (k x x)) ∨ x = (M.op x (k y y)) := by
          first
          | (have i₁ := b1e61395
             have i₂ := b1e19693
             grind)
          | exact superpose b1e19693 b1e61395
          | exact resolve b1e61395 b1e19693
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61395
        have b1e61417 : x = (M.op x x) ∨ x = y ∨ (σ y) = (σ (k x x)) := by
          first
          | (have i₁ := b1e61406
             have i₂ := b1e19693
             grind)
          | exact superpose b1e19693 b1e61406
          | exact resolve b1e61406 b1e19693
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19693 b1e61406
        have b1e61426 : x = y ∨ x = y ∨ (σ y) = (σ (k x x)) := by
          first
          | (have i₁ := b1e61417
             have i₂ := b1e40
             grind)
          | exact superpose b1e40 b1e61417
          | exact resolve b1e61417 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40 b1e61417
        have b1e61427 : (σ y) = (σ (k x x)) ∨ x = y := by grind
        clear b1e61426
        have b1e61663 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b1e3525 x x
             have i₂ := b1e61427
             grind)
          | exact superpose b1e61427 b1e3525
          | exact resolve b1e3525 b1e61427
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3525 b1e61427
        have b1e61775 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have r₁ := b1e61663
             have r₂ := b1e21
             grind)
          | exact resolve b1e61663 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61663
        have b1e62300 : y = (τ (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e61775
             grind)
          | exact superpose b1e61775 b1e13
          | exact resolve b1e13 b1e61775
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61775
        have b1e62408 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e62300
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e62300
          | exact resolve b1e62300 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62300
        have b1e62409 : x = y := by grind
        clear b1e62408
        have b1e62602 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e62409
             grind)
          | exact superpose b1e62409 b1e21
          | exact resolve b1e21 b1e62409
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e62608 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e41
             have i₂ := b1e62409
             grind)
          | exact superpose b1e62409 b1e41
          | exact resolve b1e41 b1e62409
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e62409
        have b1e62755 : False := by grind
        exact b1e62755
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X1)) X0)) = X0 := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : x ≠ x ∨ x = (k x y) := by
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
        have b2e26 : x = (k x y) := by grind
        clear b2e25
        have b2e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e27 X0 X1
             grind)
          | exact superpose b2e27 b2e13
          | exact resolve b2e13 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) (M.op (M.op X3 X0) X3)) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X3 (M.op (M.op X0 (M.op X1 X2)) X0) X2
             have i₂ := b2e12 X0 X2 X1
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 (M.op X0 (M.op x X1))
             have i₂ := b2e12 X0 X1 x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e37 : y = (M.op x x) := by
          first
          | (have i₁ := b2e35 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e35
          | exact resolve b2e35 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X1)) X0) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e35 X1 (M.op (M.op X0 (M.op X2 X1)) X0)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e35
          | exact resolve b2e35 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e40 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X2 X0) X2)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X2 (M.op X1 X0) X1
             have i₂ := b2e35 X1 X0
             grind)
          | exact superpose b2e35 b2e12
          | exact resolve b2e12 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e45 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b2e48 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e35 X1 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e35 X0 X1
             have i₂ := b2e17 (M.op X0 X1) X1
             grind)
          | exact superpose b2e17 b2e35
          | (have j1 := b2e17 X0 X1
             grind)
          | exact resolve b2e35 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e51 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op X0 (M.op X2 X1))) ∨ (k X0 (M.op X2 X1)) = (M.op (M.op X2 X1) X0) ∨ (M.op X0 (M.op X2 X1)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (M.op X2 X1) X1 X2
             have i₂ := b2e17 X0 (M.op X2 X1)
             grind)
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e17 (M.op X0 (M.op X2 X1)) X1
             grind)
          | exact superpose b2e17 b2e12
          | (have j1 := b2e17 X0 (M.op X2 X1)
             grind)
          | exact resolve b2e12 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
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
        have b2e55 : x ≠ y ∨ x = (k x x) := by
          first
          | (have i₁ := b2e15 x x
             have i₂ := b2e37
             grind)
          | exact superpose b2e37 b2e15
          | (have j0 := b2e15 x x
             grind)
          | exact resolve b2e15 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e127 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X1 X0)) (M.op X0 X1)) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e34 (M.op X1 X0) X2 X3 X1
             have i₂ := b2e35 X1 X0
             grind)
          | exact superpose b2e35 b2e34
          | exact resolve b2e34 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e141 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X1 (M.op X2 X3)) X1) X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e35 (M.op (M.op X1 (M.op X2 X3)) X1) (M.op (M.op X0 X1) X0)
             have i₂ := b2e34 X1 X2 X3 X0
             grind)
          | exact superpose b2e34 b2e35
          | exact resolve b2e35 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e145 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X0) := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e141 X0 X1 x X3
             have i₂ := b2e38 X1 X3 x
             grind)
          | exact superpose b2e38 b2e141
          | exact resolve b2e141 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e141
        have b2e158 : ∀ X0 X1 X3 : G, (M.op (M.op X3 (M.op X1 X0)) (M.op X0 X1)) = X1 := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e127 X0 X1 x X3
             have i₂ := b2e38 (M.op X1 X0) X3 x
             grind)
          | exact superpose b2e38 b2e127
          | exact resolve b2e127 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e127
        have b2e187 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e52 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e188 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e187
             have r₂ := b2e21
             grind)
          | exact resolve b2e187 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e187
        have b2e189 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e188
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e188
          | exact resolve b2e188 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e188
        have b2e190 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e189
             have i₂ := b2e26
             grind)
          | exact superpose b2e26 b2e189
          | exact resolve b2e189 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e189
        have b2e333 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e45 y y
             grind)
          | exact superpose b2e45 b2e22
          | (have j1 := b2e45 y y
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e45 y x
             grind)
          | exact resolve b2e22 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e340 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e35 (σ X1) (σ X0)
             have i₂ := b2e45 X1 X0
             grind)
          | exact superpose b2e45 b2e35
          | (have j1 := b2e45 X1 X0
             grind)
          | exact resolve b2e35 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35 b2e45
        have b2e375 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e333
        have b2e513 : ∀ X0 : G, x = (M.op y (M.op X0 x)) ∨ (k X0 x) = (M.op x X0) ∨ (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e51 X0 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e51
          | exact resolve b2e51 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51
        have b2e1002 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) X0)) = X0 ∨ (M.op X0 (M.op (M.op X0 X0) X0)) = X0 := by
          intro X0
          grind
        clear b2e40
        have b2e1013 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) X0)) = X0 := by
          intro X0
          first
          | (have j0 := b2e1002 X0
             have j1 := b2e15 X0 (M.op (M.op X0 X0) X0)
             grind)
          | (have r₁ := b2e1002 X0
             have r₂ := b2e15 X0 (M.op (M.op X0 X0) X0)
             grind)
          | exact resolve b2e1002 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1002
        have b2e1118 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e1013 X1
             have i₂ := b2e145 X1 X1 X0
             grind)
          | (have i₁ := b2e1013 X0
             have i₂ := b2e145 X0 X0 X0
             grind)
          | exact superpose b2e145 b2e1013
          | exact resolve b2e1013 b2e145
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e145 b2e1013
        have b2e1339 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have i₁ := b2e1118 x (M.op X0 X0)
             have i₂ := b2e158 X0 X0 x
             grind)
          | exact superpose b2e158 b2e1118
          | exact resolve b2e1118 b2e158
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e158 b2e1118
        have b2e1399 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
          intro X0
          first
          | (have i₁ := b2e32 (M.op (σ X0) (σ X0)) X0
             have i₂ := b2e1339 (σ X0)
             grind)
          | exact superpose b2e1339 b2e32
          | exact resolve b2e32 b2e1339
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e1339
        have b2e2418 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e375
             have i₂ := b2e17 y y
             grind)
          | exact superpose b2e17 b2e375
          | (have j1 := b2e17 (σ y) (σ y)
             grind)
          | exact resolve b2e375 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e375
        have b2e2419 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b2e2418
        have b2e4149 : y = (k x x) ∨ x = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e513 x
             have i₂ := b2e37
             grind)
          | exact superpose b2e37 b2e513
          | exact resolve b2e513 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37 b2e513
        have b2e6490 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e340 x x
             have i₂ := b2e4149
             grind)
          | exact superpose b2e4149 b2e340
          | (have j0 := b2e340 x x
             grind)
          | exact resolve b2e340 b2e4149
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e340
        have b2e6542 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = y := by grind
        clear b2e6490
        have b2e6556 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
          first
          | (have r₁ := b2e6542
             have r₂ := b2e21
             grind)
          | exact resolve b2e6542 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6542
        have b2e52770 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e1399 x
             have i₂ := b2e6556
             grind)
          | exact superpose b2e6556 b2e1399
          | exact resolve b2e1399 b2e6556
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6556
        have b2e52892 : x = (k x x) ∨ x = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e52770
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e52770
          | exact resolve b2e52770 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52770
        have b2e52897 : x = (k x x) ∨ x = (M.op y y) := by
          first
          | (have r₁ := b2e52892
             have r₂ := b2e55
             grind)
          | exact resolve b2e52892 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55 b2e52892
        have b2e53082 : x = y ∨ x = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
          first
          | (have i₁ := b2e4149
             have i₂ := b2e52897
             grind)
          | exact superpose b2e52897 b2e4149
          | exact resolve b2e4149 b2e52897
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4149 b2e52897
        have b2e53118 : x = (M.op y y) ∨ x = y := by grind
        clear b2e53082
        have b2e54921 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = y := by
          first
          | (have i₁ := b2e2419
             have i₂ := b2e53118
             grind)
          | exact superpose b2e53118 b2e2419
          | exact resolve b2e2419 b2e53118
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2419
        have b2e54925 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
        clear b2e54921
        have b2e54926 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
        clear b2e54925
        have b2e54947 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = y := by
          first
          | (have i₁ := b2e1399 y
             have i₂ := b2e54926
             grind)
          | exact superpose b2e54926 b2e1399
          | exact resolve b2e1399 b2e54926
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1399 b2e54926
        have b2e55074 : y = (k y y) ∨ x = y := by
          first
          | (have i₁ := b2e54947
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e54947
          | exact resolve b2e54947 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54947
        have b2e55367 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e48 y y
             have i₂ := b2e55074
             grind)
          | exact superpose b2e55074 b2e48
          | (have j0 := b2e48 y y
             grind)
          | exact resolve b2e48 b2e55074
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48 b2e55074
        have b2e55376 : y = (M.op y y) ∨ x = y := by grind
        clear b2e55367
        have b2e55609 : x = y ∨ x = y ∨ x = y := by
          first
          | (have i₁ := b2e53118
             have i₂ := b2e55376
             grind)
          | exact superpose b2e55376 b2e53118
          | exact resolve b2e53118 b2e55376
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53118 b2e55376
        have b2e55731 : x = y := by grind
        clear b2e55609
        have b2e56274 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e55731
             grind)
          | exact superpose b2e55731 b2e22
          | exact resolve b2e22 b2e55731
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e56288 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e190
             have i₂ := b2e55731
             grind)
          | exact superpose b2e55731 b2e190
          | exact resolve b2e190 b2e55731
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e190 b2e55731
        have b2e56357 : False := by grind
        exact b2e56357
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X1)) X0)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
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
        have b3e40 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 X0 (M.op X0 (M.op x X1))
             have i₂ := b3e12 X0 X1 x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b3e51 : y = (M.op y x) := by
          first
          | (have i₁ := b3e40 y y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e40
          | exact resolve b3e40 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e52 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e40 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e40
          | exact resolve b3e40 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e59 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e60 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e59 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
        have b3e61 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e60 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e60 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e60 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60
        have b3e417 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e45 x x
             have i₂ := b3e52
             grind)
          | exact superpose b3e52 b3e45
          | exact resolve b3e45 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e52
        have b3e468 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e417
        have b3e7839 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e468
             grind)
          | exact superpose b3e468 b3e13
          | exact resolve b3e13 b3e468
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e468
        have b3e7874 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e7839
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e7839
          | exact resolve b3e7839 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7839
        have b3e7987 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e61 x x
             have i₂ := b3e7874
             grind)
          | exact superpose b3e7874 b3e61
          | exact resolve b3e61 b3e7874
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61 b3e7874
        have b3e15658 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e40 x x
             have i₂ := b3e7987
             grind)
          | exact superpose b3e7987 b3e40
          | exact resolve b3e40 b3e7987
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40 b3e7987
        have b3e15714 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have r₁ := b3e15658
             have r₂ := b3e20
             grind)
          | exact resolve b3e15658 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e15658
        have b3e16335 : y = (τ (σ x)) ∨ x = y := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e15714
             grind)
          | exact superpose b3e15714 b3e13
          | exact resolve b3e13 b3e15714
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e15714
        have b3e16435 : x = y ∨ x = y := by
          first
          | (have i₁ := b3e16335
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e16335
          | exact resolve b3e16335 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e16335
        have b3e16436 : x = y := by grind
        clear b3e16435
        have b3e17048 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e16436
             grind)
          | exact superpose b3e16436 b3e24
          | exact resolve b3e24 b3e16436
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e17054 : x = (M.op x x) := by
          first
          | (have i₁ := b3e51
             have i₂ := b3e16436
             grind)
          | exact superpose b3e16436 b3e51
          | exact resolve b3e51 b3e16436
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51 b3e16436
        have b3e17130 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e17048
             have i₂ := b3e17054
             grind)
          | exact superpose b3e17054 b3e17048
          | exact resolve b3e17048 b3e17054
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e17048 b3e17054
        have b3e17131 : False := by grind
        exact b3e17131
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X1)) X0)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e34 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e29 X0 X1
               grind)
            | exact superpose b4e29 b4e14
            | exact resolve b4e14 b4e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29
          have b4e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) (M.op (M.op X3 X0) X3)) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X3 (M.op (M.op X0 (M.op X1 X2)) X0) X2
               have i₂ := b4e13 X0 X2 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0 (M.op X0 (M.op x X1))
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : y = (M.op y x) := by
            first
            | (have i₁ := b4e38 y y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e38
            | exact resolve b4e38 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e38 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e38
            | exact resolve b4e38 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X1)) X0) = (M.op X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e38 X1 (M.op (M.op X0 (M.op X2 X1)) X0)
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e38
            | exact resolve b4e38 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b4e57 : ∀ X0 : G, (M.op x (M.op (M.op X0 y) X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 x y
               have i₂ := b4e40
               grind)
            | exact superpose b4e40 b4e13
            | exact resolve b4e13 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e62 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e63 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e62 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62
          have b4e64 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e63 X0 X1
               have j1 := b4e16 X0 X1
               grind)
            | (have r₁ := b4e63 X0 X1
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e63 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e63
          have b4e88 : ∀ X0 : G, (M.op (σ x) (M.op (M.op X0 (σ y)) X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ x) (σ y)
               have i₂ := b4e41
               grind)
            | exact superpose b4e41 b4e13
            | exact resolve b4e13 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e110 : ∀ X0 : G, (M.op (M.op X0 y) X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e38 x (M.op (M.op X0 y) X0)
               have i₂ := b4e57 X0
               grind)
            | exact superpose b4e57 b4e38
            | exact resolve b4e38 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57
          have b4e115 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e30 X0 X1
               have i₂ := b4e64 X1 (τ X0)
               grind)
            | exact superpose b4e64 b4e30
            | (have j1 := b4e64 X1 (τ X0)
               grind)
            | exact resolve b4e30 b4e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64
          have b4e180 : ∀ X0 X1 : G, y = (M.op (M.op (M.op y (M.op X0 X1)) y) (M.op x y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e37 y X0 X1 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e37
            | exact resolve b4e37 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e201 : ∀ X1 : G, y = (M.op (M.op X1 y) (M.op x y)) := by
            intro X1
            first
            | (have i₁ := b4e180 x X1
               have i₂ := b4e42 y X1 x
               grind)
            | exact superpose b4e42 b4e180
            | exact resolve b4e180 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e180
          have b4e422 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e18 X1 (σ X0)
               have i₂ := b4e49 X0 X0
               grind)
            | exact superpose b4e49 b4e18
            | (have j0 := b4e18 X1 (σ X0)
               have j1 := b4e49 X0 X0
               grind)
            | exact resolve b4e18 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e454 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e49 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49
          have b4e455 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e454 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e454
          have b4e459 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e422 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e422
          have b4e626 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op y (M.op X1 X2)) y) (M.op x X0)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e37 y X1 X2 X0
               have i₂ := b4e110 X0
               grind)
            | exact superpose b4e110 b4e37
            | exact resolve b4e37 b4e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e110
          have b4e651 : ∀ X0 X2 : G, (M.op (M.op X2 y) (M.op x X0)) = X0 := by
            intro X0 X2
            first
            | (have i₁ := b4e626 X0 x X2
               have i₂ := b4e42 y X2 x
               grind)
            | exact superpose b4e42 b4e626
            | exact resolve b4e626 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e626
          have b4e2757 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op (τ X1) X0)) X1) ∨ (M.op (τ X1) X0) = (k (M.op (τ X1) X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e115 X1 (M.op (τ X1) X0)
               have i₂ := b4e38 (τ X1) X0
               grind)
            | exact superpose b4e38 b4e115
            | (have j0 := b4e115 X1 (M.op (τ X1) X0)
               grind)
            | exact resolve b4e115 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115
          have b4e13024 : ∀ X0 X1 : G, (σ X1) ≠ X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e455 X1
               have i₂ := b4e459 X1 X0
               grind)
            | (have i₁ := b4e455 X0
               have i₂ := b4e459 X0 (σ (k X0 X0))
               grind)
            | exact superpose b4e459 b4e455
            | (have j0 := b4e455 X1
               have j1 := b4e459 X1 X0
               grind)
            | (have r₁ := b4e455 (k X0 X0)
               have r₂ := b4e459 X0 (σ (k (k X0 X0) (k X0 X0)))
               grind)
            | (have r₁ := b4e455 X0
               have r₂ := b4e459 X0 (σ X0)
               grind)
            | exact resolve b4e455 b4e459
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e455 b4e459
          have b4e13086 : ∀ X0 X1 : G, (σ X1) ≠ X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e13024 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13024
          have b4e77915 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X1)) X0))) X1) ∨ (M.op (τ (σ X1)) X0) = (k (M.op (τ (σ X1)) X0) (τ (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e34 (σ (M.op (τ (σ X1)) X0)) X1
               have i₂ := b4e2757 X0 (σ X1)
               grind)
            | exact superpose b4e2757 b4e34
            | (have j1 := b4e2757 X0 (σ X1)
               grind)
            | exact resolve b4e34 b4e2757
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e2757
          have b4e77918 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X1)) X0) X1) ∨ (M.op (τ (σ X1)) X0) = (k (M.op (τ (σ X1)) X0) (τ (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e77915 X0 X1
               have i₂ := b4e14 (M.op (τ (σ X1)) X0)
               grind)
            | exact superpose b4e14 b4e77915
            | (have j0 := b4e77915 X0 X1
               grind)
            | exact resolve b4e77915 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77915
          have b4e77931 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X1 X0) X1) ∨ (M.op (τ (σ X1)) X0) = (k (M.op (τ (σ X1)) X0) (τ (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e77918 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e77918
            | (have j0 := b4e77918 X0 X1
               grind)
            | exact resolve b4e77918 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77918
          have b4e77934 : ∀ X0 X1 : G, (k (M.op X1 X0) X1) = X0 ∨ (M.op (τ (σ X1)) X0) = (k (M.op (τ (σ X1)) X0) (τ (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e77931 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e77931
            | (have j0 := b4e77931 X0 X1
               grind)
            | exact resolve b4e77931 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77931
          have b4e77935 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X1) ∨ (k (M.op X1 X0) X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e77934 X0 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e77934
            | (have j0 := b4e77934 X0 X1
               grind)
            | exact resolve b4e77934 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77934
          have b4e78057 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X0 X1) X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e77935 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77935
          have b4e78278 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e78057 X0 (M.op X0 X1)
               have i₂ := b4e38 X0 X1
               grind)
            | exact superpose b4e38 b4e78057
            | (have j0 := b4e78057 X1 X0
               grind)
            | exact resolve b4e78057 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78057
          have b4e102652 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e13086 (σ X0) X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13086
          have b4e102653 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e102652 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102652
          have b4e102654 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e102653 X0
               have j1 := b4e78278 (σ X0) (σ X0)
               grind)
            | (have r₁ := b4e102653 X0
               have r₂ := b4e78278 (σ X0) (σ X0)
               grind)
            | exact resolve b4e102653 b4e78278
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78278 b4e102653
          have b4e102655 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e102654 X0
               have i₂ := b4e19 X0 X0
               grind)
            | exact superpose b4e19 b4e102654
            | exact resolve b4e102654 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102654
          have b4e102658 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e102655 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e102655
            | exact resolve b4e102655 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e102824 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e38 (σ X0) (σ X0)
               have i₂ := b4e102655 X0
               grind)
            | exact superpose b4e102655 b4e38
            | exact resolve b4e38 b4e102655
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e103028 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b4e102658 X0
               have i₂ := b4e30 X0 (τ X0)
               grind)
            | exact superpose b4e30 b4e102658
            | exact resolve b4e102658 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e102658
          have b4e103059 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b4e103028 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e103028
            | exact resolve b4e103028 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e103028
          have b4e104425 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e102824 X0
               have i₂ := b4e103059 X0
               grind)
            | exact superpose b4e103059 b4e102824
            | exact resolve b4e102824 b4e103059
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102824
          have b4e105710 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
            first
            | (have i₁ := b4e104425 (M.op x y)
               have i₂ := b4e651 y x
               grind)
            | exact superpose b4e651 b4e104425
            | exact resolve b4e104425 b4e651
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e651 b4e104425
          have b4e110700 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
            first
            | (have i₁ := b4e88 (σ (M.op x y))
               have i₂ := b4e105710
               grind)
            | exact superpose b4e105710 b4e88
            | exact resolve b4e88 b4e105710
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e88 b4e105710
          have b4e110844 : (σ (M.op x y)) = (M.op (σ x) (σ (k (M.op x y) (M.op x y)))) := by
            first
            | (have i₁ := b4e110700
               have i₂ := b4e102655 (M.op x y)
               grind)
            | exact superpose b4e102655 b4e110700
            | exact resolve b4e110700 b4e102655
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102655 b4e110700
          have b4e110866 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) := by
            first
            | (have i₁ := b4e110844
               have i₂ := b4e103059 (M.op x y)
               grind)
            | exact superpose b4e103059 b4e110844
            | exact resolve b4e110844 b4e103059
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e103059 b4e110844
          have b4e110877 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e110866
               have i₂ := b4e201 x
               grind)
            | exact superpose b4e201 b4e110866
            | exact resolve b4e110866 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e201 b4e110866
          have b4e110881 : False := by grind
          exact b4e110881
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X1)) X0)) = X0 := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : x ≠ y ∨ y = (k y y) := by
            first
            | (have i₁ := b5e16 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 y y
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e35 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 (M.op X0 (M.op x X1))
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X1 (M.op (M.op X0 (M.op X2 X1)) X0)) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 X1 (M.op (M.op X0 (M.op X2 X1)) X0)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e16
            | (have j0 := b5e16 X1 (M.op (M.op X0 (M.op X2 X1)) X0)
               grind)
            | (have r₁ := b5e16 X0 (M.op (M.op X0 (M.op X2 X0)) X0)
               have r₂ := b5e13 X0 X0 X2
               grind)
            | exact resolve b5e16 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X1)) X0) = (M.op X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e35 X1 (M.op (M.op X0 (M.op X2 X1)) X0)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e35
            | exact resolve b5e35 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e50 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 (M.op (σ y) (σ y)) x
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
          have b5e55 : x = (k x y) ∨ x = (M.op x y) := by grind
          have b5e59 : x = (k x y) := by
            first
            | (have j1 := b5e16 x y
               grind)
            | (have r₁ := b5e55
               have r₂ := b5e16 x y
               grind)
            | exact resolve b5e55 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e76 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e28 X1 X0
               grind)
            | exact superpose b5e28 b5e14
            | exact resolve b5e14 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e103 : ∀ X0 X1 : G, (k X0 (M.op (M.op X0 (M.op X1 X0)) X0)) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e36 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e104 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e103 X0 x
               have i₂ := b5e38 X0 X0 x
               grind)
            | exact superpose b5e38 b5e103
            | exact resolve b5e103 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38 b5e103
          have b5e187 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e50 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e188 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e187
               have r₂ := b5e23
               grind)
            | exact resolve b5e187 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e187
          have b5e189 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e188
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e188
            | exact resolve b5e188 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e188
          have b5e190 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e189
               have i₂ := b5e59
               grind)
            | exact superpose b5e59 b5e189
            | exact resolve b5e189 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59 b5e189
          have b5e328 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e44 y y
               grind)
            | exact superpose b5e44 b5e24
            | (have j1 := b5e44 y y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e44 y x
               grind)
            | exact resolve b5e24 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e370 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e328
          have b5e641 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            first
            | (have i₁ := b5e76 X0 (M.op (σ X0) (σ X0))
               have i₂ := b5e104 (σ X0)
               grind)
            | exact superpose b5e104 b5e76
            | exact resolve b5e76 b5e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76 b5e104
          have b5e649 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e641 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e641
            | exact resolve b5e641 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e641
          have b5e1850 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e370
               have i₂ := b5e18 y y
               grind)
            | exact superpose b5e18 b5e370
            | (have j1 := b5e18 (σ y) (σ y)
               grind)
            | exact resolve b5e370 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e370
          have b5e1851 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
          clear b5e1850
          have b5e1852 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e1851
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1851
            | exact resolve b5e1851 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1851
          have b5e1853 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
          clear b5e1852
          have b5e1860 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b5e1853
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1853
            | exact resolve b5e1853 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1853
          have b5e3963 : y = (k y (τ (σ y))) ∨ x = y := by
            first
            | (have i₁ := b5e649 y
               have i₂ := b5e1860
               grind)
            | exact superpose b5e1860 b5e649
            | exact resolve b5e649 b5e1860
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e649 b5e1860
          have b5e4015 : y = (k y y) ∨ x = y := by
            first
            | (have i₁ := b5e3963
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e3963
            | exact resolve b5e3963 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3963
          have b5e4017 : y = (k y y) := by
            first
            | (have r₁ := b5e4015
               have r₂ := b5e26
               grind)
            | exact resolve b5e4015 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e4015
          have b5e4103 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e18 y y
               have i₂ := b5e4017
               grind)
            | exact superpose b5e4017 b5e18
            | (have j0 := b5e18 y y
               grind)
            | exact resolve b5e18 b5e4017
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4017
          have b5e4104 : y = (M.op y y) := by grind
          clear b5e4103
          have b5e4116 : x = y := by
            first
            | (have i₁ := b5e4104
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e4104
            | exact resolve b5e4104 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4104
          have b5e4217 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e4116
               grind)
            | exact superpose b5e4116 b5e24
            | exact resolve b5e24 b5e4116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4232 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e190
               have i₂ := b5e4116
               grind)
            | exact superpose b5e4116 b5e190
            | exact resolve b5e190 b5e4116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e190 b5e4116
          have b5e4253 : False := by grind
          exact b5e4253
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X1)) X0)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op y y) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e25 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b6e26 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b6e25
        have b6e27 : (σ x) = (σ (k x y)) := by
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
        have b6e32 : (k x y) = (τ (σ x)) := by
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
        have b6e33 : x = (k x y) := by
          first
          | (have i₁ := b6e32
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e32
          | exact resolve b6e32 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e38 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 X0 (M.op X0 (M.op x X1))
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e43 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b6e44 : x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
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
        have b6e50 : x = (M.op y x) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b6e44
             have r₂ := b6e21
             grind)
          | exact resolve b6e44 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e53 : x = (M.op y x) := by
          first
          | (have r₁ := b6e50
             have r₂ := b6e20
             grind)
          | exact resolve b6e50 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e57 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e58 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e58 X0 X1
             have j1 := b6e15 X0 X1
             grind)
          | (have r₁ := b6e58 X0 X1
             have r₂ := b6e15 X0 X1
             grind)
          | exact resolve b6e58 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e60 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e38 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e38
          | exact resolve b6e38 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e62 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e38 X1 X1
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e38 X0 X1
             have i₂ := b6e17 (M.op X0 X1) X1
             grind)
          | exact superpose b6e17 b6e38
          | (have j1 := b6e17 X0 X1
             grind)
          | exact resolve b6e38 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e89 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
        have b6e95 : (σ y) = (k (σ y) (σ x)) := by
          first
          | (have j1 := b6e15 (σ y) (σ x)
             grind)
          | (have r₁ := b6e89
             have r₂ := b6e15 (σ y) (σ x)
             grind)
          | exact resolve b6e89 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e89
        have b6e96 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e95
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e95
          | exact resolve b6e95 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95
        have b6e106 : (k y x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e96
             grind)
          | exact superpose b6e96 b6e13
          | exact resolve b6e13 b6e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e96
        have b6e107 : y = (k y x) := by
          first
          | (have i₁ := b6e106
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e106
          | exact resolve b6e106 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e106
        have b6e311 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e43 x x
             have i₂ := b6e60
             grind)
          | exact superpose b6e60 b6e43
          | exact resolve b6e43 b6e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43 b6e60
        have b6e362 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e311
        have b6e2494 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e107
             have i₂ := b6e62 y x
             grind)
          | exact superpose b6e62 b6e107
          | (have j1 := b6e62 y x
             grind)
          | exact resolve b6e107 b6e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62 b6e107
        have b6e2501 : y = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e2494
             have r₂ := b6e20
             grind)
          | exact resolve b6e2494 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2494
        have b6e2504 : y = (M.op x y) ∨ x = y := by
          first
          | (have i₁ := b6e2501
             have i₂ := b6e53
             grind)
          | exact superpose b6e53 b6e2501
          | exact resolve b6e2501 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2501
        have b6e2507 : (σ x) ≠ (σ y) ∨ x = y := by
          first
          | (have i₁ := b6e24
             have i₂ := b6e2504
             grind)
          | exact superpose b6e2504 b6e24
          | exact resolve b6e24 b6e2504
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2504
        have b6e8297 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e362
             grind)
          | exact superpose b6e362 b6e13
          | exact resolve b6e13 b6e362
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e362
        have b6e8348 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e8297
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e8297
          | exact resolve b6e8297 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8297
        have b6e8453 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e59 x x
             have i₂ := b6e8348
             grind)
          | exact superpose b6e8348 b6e59
          | exact resolve b6e59 b6e8348
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59 b6e8348
        have b6e8461 : y = (M.op x x) ∨ x = y := by
          first
          | (have r₁ := b6e8453
             have r₂ := b6e2507
             grind)
          | exact resolve b6e8453 b6e2507
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2507 b6e8453
        have b6e8580 : x = (M.op x y) ∨ x = y := by
          first
          | (have i₁ := b6e38 x x
             have i₂ := b6e8461
             grind)
          | exact superpose b6e8461 b6e38
          | exact resolve b6e38 b6e8461
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38 b6e8461
        have b6e8633 : x = y := by
          first
          | (have r₁ := b6e8580
             have r₂ := b6e20
             grind)
          | exact resolve b6e8580 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8580
        have b6e8737 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e24
             have i₂ := b6e8633
             grind)
          | exact superpose b6e8633 b6e24
          | exact resolve b6e24 b6e8633
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e8742 : x = (M.op x x) := by
          first
          | (have i₁ := b6e53
             have i₂ := b6e8633
             grind)
          | exact superpose b6e8633 b6e53
          | exact resolve b6e53 b6e8633
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53 b6e8633
        have b6e8781 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b6e8737
             have i₂ := b6e8742
             grind)
          | exact superpose b6e8742 b6e8737
          | exact resolve b6e8737 b6e8742
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8737 b6e8742
        have b6e8782 : False := by grind
        exact b6e8782
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X1)) X0)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e32 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X0 (M.op X0 (M.op x X1))
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e32 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e32
            | exact resolve b7e32 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e42 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X1 X0
               have i₂ := b7e18 (σ X1) (σ X0)
               grind)
            | exact superpose b7e18 b7e19
            | (have j1 := b7e18 (σ X1) (σ X0)
               grind)
            | exact resolve b7e19 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e54 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e55 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e54 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e55 X0 X1
               have j1 := b7e16 X0 X1
               grind)
            | (have r₁ := b7e55 X0 X1
               have r₂ := b7e16 X0 X1
               grind)
            | exact resolve b7e55 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e350 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e42 y y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e42
            | exact resolve b7e42 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e401 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e350
          have b7e1369 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e401
               grind)
            | exact superpose b7e401 b7e14
            | exact resolve b7e14 b7e401
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e401
          have b7e1384 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e1369
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1369
            | exact resolve b7e1369 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1369
          have b7e1574 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e56 y y
               have i₂ := b7e1384
               grind)
            | exact superpose b7e1384 b7e56
            | exact resolve b7e56 b7e1384
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56 b7e1384
          have b7e1579 : (σ x) = (σ y) ∨ x = y := by
            first
            | (have r₁ := b7e1574
               have r₂ := b7e22
               grind)
            | exact resolve b7e1574 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1574
          have b7e1644 : y = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e1579
               grind)
            | exact superpose b7e1579 b7e14
            | exact resolve b7e14 b7e1579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1579
          have b7e1664 : x = y ∨ x = y := by
            first
            | (have i₁ := b7e1644
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1644
            | exact resolve b7e1644 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1644
          have b7e1665 : x = y := by grind
          clear b7e1664
          have b7e1746 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e1665
               grind)
            | exact superpose b7e1665 b7e23
            | exact resolve b7e23 b7e1665
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1750 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e34
               have i₂ := b7e1665
               grind)
            | exact superpose b7e1665 b7e34
            | exact resolve b7e34 b7e1665
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e1665
          have b7e1766 : False := by grind
          exact b7e1766
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X1)) X0)) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x y) := by grind
          have b8e22 : x ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
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
          have b8e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b8e29 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 X0 (M.op X0 (M.op x X1))
               have i₂ := b8e13 X0 X1 x
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e37 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b8e38 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e29 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e29 X0 X1
               have i₂ := b8e18 (M.op X0 X1) X1
               grind)
            | exact superpose b8e18 b8e29
            | (have j1 := b8e18 X0 X1
               grind)
            | exact resolve b8e29 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e42 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
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
          have b8e44 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 X0) ∨ (τ X1) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e18 (τ X1) X0
               grind)
            | exact superpose b8e18 b8e26
            | (have j1 := b8e18 (τ X1) X0
               grind)
            | exact resolve b8e26 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b8e48 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e49 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e48 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e48
          have b8e50 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e49 X0 X1
               have j1 := b8e16 X0 X1
               grind)
            | (have r₁ := b8e49 X0 X1
               have r₂ := b8e16 X0 X1
               grind)
            | exact resolve b8e49 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49
          have b8e53 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
            intro X0
            grind
          have b8e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e50 (σ X0) (σ X1)
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e50
            | exact resolve b8e50 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e62 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e27 X0 X1
               have i₂ := b8e50 X1 (τ X0)
               grind)
            | exact superpose b8e50 b8e27
            | (have j1 := b8e50 X1 (τ X0)
               grind)
            | exact resolve b8e27 b8e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e66 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e50 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50
          have b8e123 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e42 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42
          have b8e124 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b8e123
               have r₂ := b8e23
               grind)
            | exact resolve b8e123 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e123
          have b8e125 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e124
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e124
            | exact resolve b8e124 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e124
          have b8e190 : (σ x) = (M.op (σ y) (σ (k x y))) := by
            first
            | (have i₁ := b8e29 (σ y) (σ x)
               have i₂ := b8e125
               grind)
            | exact superpose b8e125 b8e29
            | exact resolve b8e29 b8e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e260 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e125
               have i₂ := b8e37 x y
               grind)
            | exact superpose b8e37 b8e125
            | (have j1 := b8e37 x y
               grind)
            | exact resolve b8e125 b8e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e269 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e37 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37
          have b8e270 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e269 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e269
          have b8e362 : (σ x) = (M.op (σ y) (σ (M.op y x))) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e190
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e190
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e190 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e190
          have b8e373 : (σ x) = (M.op (σ y) (σ (M.op y x))) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e362
               have r₂ := b8e22
               grind)
            | exact resolve b8e362 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e362
          have b8e376 : (σ x) = (M.op (σ y) (σ (M.op y x))) := by
            first
            | (have r₁ := b8e373
               have r₂ := b8e21
               grind)
            | exact resolve b8e373 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e373
          have b8e826 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b8e29 (σ y) (σ (M.op y x))
               have i₂ := b8e376
               grind)
            | exact superpose b8e376 b8e29
            | exact resolve b8e29 b8e376
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e878 : (σ (k x y)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b8e125
               have i₂ := b8e826
               grind)
            | exact superpose b8e826 b8e125
            | exact resolve b8e125 b8e826
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e125 b8e826
          have b8e1192 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e270 (τ X0)
               have i₂ := b8e27 X0 (τ X0)
               grind)
            | exact superpose b8e27 b8e270
            | (have j0 := b8e270 (τ X0)
               grind)
            | exact resolve b8e270 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27 b8e270
          have b8e1195 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e1192 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e1192
            | (have j0 := b8e1192 X0
               grind)
            | exact resolve b8e1192 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1192
          have b8e1198 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e1195 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e1195
            | (have j0 := b8e1195 X0
               grind)
            | exact resolve b8e1195 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1195
          have b8e1336 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e62 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e62
            | exact resolve b8e62 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1341 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op (τ X1) X0)) X1) ∨ (M.op (τ X1) X0) = (k (M.op (τ X1) X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e62 X1 (M.op (τ X1) X0)
               have i₂ := b8e29 (τ X1) X0
               grind)
            | exact superpose b8e29 b8e62
            | (have j0 := b8e62 X1 (M.op (τ X1) X0)
               grind)
            | exact resolve b8e62 b8e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e1376 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e1336 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e1336
            | (have j0 := b8e1336 X0 X1
               grind)
            | exact resolve b8e1336 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1336
          have b8e1762 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e61 y x
               grind)
            | exact superpose b8e61 b8e20
            | (have j1 := b8e61 y x
               grind)
            | exact resolve b8e20 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3802 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e44 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e44
            | exact resolve b8e44 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44
          have b8e3980 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e3802 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e3802
            | (have j0 := b8e3802 X0 X1
               grind)
            | exact resolve b8e3802 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3802
          have b8e6979 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (M.op X0 (τ X1)) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e53 X0
               have i₂ := b8e18 X0 (τ X0)
               grind)
            | (have i₁ := b8e53 X0
               have i₂ := b8e18 (M.op (τ X0) (τ X0)) X1
               grind)
            | exact superpose b8e18 b8e53
            | (have j1 := b8e18 X0 (τ X1)
               grind)
            | exact resolve b8e53 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e7016 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (M.op X0 (τ X1)) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have j0 := b8e6979 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6979
          have b8e40702 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e1762
               have i₂ := b8e1376 x y
               grind)
            | exact superpose b8e1376 b8e1762
            | (have j1 := b8e1376 x y
               grind)
            | (have r₁ := b8e1762
               have r₂ := b8e1376 x y
               grind)
            | exact resolve b8e1762 b8e1376
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1376 b8e1762
          have b8e40703 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by grind
          clear b8e40702
          have b8e40710 : (M.op x y) = (τ (σ y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e14 (M.op x y)
               have i₂ := b8e40703
               grind)
            | exact superpose b8e40703 b8e14
            | exact resolve b8e14 b8e40703
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40703
          have b8e40799 : y = (M.op x y) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e40710
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e40710
            | exact resolve b8e40710 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40710
          have b8e40800 : y = (k y x) := by
            first
            | (have j1 := b8e66 y x
               grind)
            | (have r₁ := b8e40799
               have r₂ := b8e66 y x
               grind)
            | exact resolve b8e40799 b8e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66 b8e40799
          have b8e40999 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e38 y x
               have i₂ := b8e40800
               grind)
            | exact superpose b8e40800 b8e38
            | (have j0 := b8e38 y x
               grind)
            | exact resolve b8e38 b8e40800
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38
          have b8e41008 : y = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e40999
               have r₂ := b8e21
               grind)
            | exact resolve b8e40999 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40999
          have b8e41417 : x = (M.op y y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e29 y x
               have i₂ := b8e41008
               grind)
            | exact superpose b8e41008 b8e29
            | exact resolve b8e29 b8e41008
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41008
          have b8e41488 : y = (M.op x y) := by
            first
            | (have r₁ := b8e41417
               have r₂ := b8e22
               grind)
            | exact resolve b8e41417 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41417
          have b8e56446 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X1)) X0))) X1) ∨ (M.op (τ (σ X1)) X0) = (k (M.op (τ (σ X1)) X0) (τ (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e47 (σ (M.op (τ (σ X1)) X0)) X1
               have i₂ := b8e1341 X0 (σ X1)
               grind)
            | exact superpose b8e1341 b8e47
            | (have j1 := b8e1341 X0 (σ X1)
               grind)
            | exact resolve b8e47 b8e1341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47 b8e1341
          have b8e56450 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X1)) X0) X1) ∨ (M.op (τ (σ X1)) X0) = (k (M.op (τ (σ X1)) X0) (τ (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e56446 X0 X1
               have i₂ := b8e14 (M.op (τ (σ X1)) X0)
               grind)
            | exact superpose b8e14 b8e56446
            | (have j0 := b8e56446 X0 X1
               grind)
            | exact resolve b8e56446 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56446
          have b8e56463 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X1 X0) X1) ∨ (M.op (τ (σ X1)) X0) = (k (M.op (τ (σ X1)) X0) (τ (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e56450 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e56450
            | (have j0 := b8e56450 X0 X1
               grind)
            | exact resolve b8e56450 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56450
          have b8e56466 : ∀ X0 X1 : G, (k (M.op X1 X0) X1) = X0 ∨ (M.op (τ (σ X1)) X0) = (k (M.op (τ (σ X1)) X0) (τ (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e56463 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e56463
            | (have j0 := b8e56463 X0 X1
               grind)
            | exact resolve b8e56463 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56463
          have b8e56467 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X1) ∨ (k (M.op X1 X0) X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e56466 X0 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e56466
            | (have j0 := b8e56466 X0 X1
               grind)
            | exact resolve b8e56466 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56466
          have b8e56565 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X0 X1) X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e56467 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56467
          have b8e56807 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e56565 X0 (M.op X0 X1)
               have i₂ := b8e29 X0 X1
               grind)
            | exact superpose b8e29 b8e56565
            | (have j0 := b8e56565 X1 X0
               grind)
            | exact resolve b8e56565 b8e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56565
          have b8e59090 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 (τ (σ X0))) = X0 ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b8e1198 (σ X0)
               have i₂ := b8e7016 X0 (σ X0)
               grind)
            | exact superpose b8e7016 b8e1198
            | (have j0 := b8e1198 (σ X0)
               have j1 := b8e7016 X0 (σ X0)
               grind)
            | (have r₁ := b8e1198 (σ X0)
               have r₂ := b8e7016 X0 (σ X0)
               grind)
            | exact resolve b8e1198 b8e7016
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1198 b8e7016
          have b8e59093 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 (τ (σ X0))) = X0 ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
            intro X0
            first
            | (have j0 := b8e59090 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59090
          have b8e59095 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b8e59093 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e59093
            | (have j0 := b8e59093 X0
               grind)
            | exact resolve b8e59093 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59093
          have b8e59105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e59095 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e59095
            | (have j0 := b8e59095 X0
               grind)
            | exact resolve b8e59095 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59095
          have b8e59110 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e59105 X0
               have j1 := b8e56807 X0 X0
               grind)
            | (have r₁ := b8e59105 X0
               have r₂ := b8e56807 X0 X0
               grind)
            | (have r₁ := b8e59105 X0
               have r₂ := b8e56807 (σ X0) (σ X0)
               grind)
            | exact resolve b8e59105 b8e56807
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59105
          have b8e59627 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b8e61 X0 X0
               have i₂ := b8e59110 X0
               grind)
            | exact superpose b8e59110 b8e61
            | (have j0 := b8e61 X0 X0
               have j1 := b8e59110 X0
               grind)
            | exact resolve b8e61 b8e59110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61 b8e59110
          have b8e59758 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e59627 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59627
          have b8e60188 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b8e3980 X0 X0
               have i₂ := b8e59758 X0
               grind)
            | exact superpose b8e59758 b8e3980
            | (have j0 := b8e3980 X0 X0
               have j1 := b8e59758 X0
               grind)
            | exact resolve b8e3980 b8e59758
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3980 b8e59758
          have b8e60246 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e60188 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60188
          have b8e60274 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e60246 X0
               have j1 := b8e56807 X0 X0
               grind)
            | (have r₁ := b8e60246 X0
               have r₂ := b8e56807 X0 X0
               grind)
            | exact resolve b8e60246 b8e56807
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60246
          have b8e60613 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op X0 X0)
               have i₂ := b8e60274 X0
               grind)
            | exact superpose b8e60274 b8e14
            | (have j1 := b8e60274 X0
               grind)
            | exact resolve b8e14 b8e60274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60274
          have b8e60681 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b8e60613 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e60613
            | (have j0 := b8e60613 X0
               grind)
            | exact resolve b8e60613 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60613
          have b8e60689 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e60681 X0
               have j1 := b8e56807 X0 X0
               grind)
            | (have r₁ := b8e60681 X0
               have r₂ := b8e56807 X0 X0
               grind)
            | exact resolve b8e60681 b8e56807
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56807 b8e60681
          have b8e60840 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e60689 (σ X0)
               grind)
            | exact superpose b8e60689 b8e19
            | exact resolve b8e19 b8e60689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e60904 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e60840 X0
               have i₂ := b8e60689 X0
               grind)
            | exact superpose b8e60689 b8e60840
            | exact resolve b8e60840 b8e60689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60689 b8e60840
          have b8e61432 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b8e29 (σ X0) (σ X0)
               have i₂ := b8e60904 X0
               grind)
            | exact superpose b8e60904 b8e29
            | exact resolve b8e29 b8e60904
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29
          have b8e69391 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e260
               grind)
            | exact superpose b8e260 b8e20
            | exact resolve b8e20 b8e260
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e260
          have b8e69434 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e69391
               have i₂ := b8e40800
               grind)
            | exact superpose b8e40800 b8e69391
            | exact resolve b8e69391 b8e40800
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40800 b8e69391
          have b8e69453 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e69434
               have i₂ := b8e41488
               grind)
            | exact superpose b8e41488 b8e69434
            | exact resolve b8e69434 b8e41488
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41488 b8e69434
          have b8e69454 : (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
          clear b8e69453
          have b8e69469 : (σ y) = (σ (M.op y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e69454
               have i₂ := b8e878
               grind)
            | exact superpose b8e878 b8e69454
            | exact resolve b8e69454 b8e878
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e878 b8e69454
          have b8e69470 : (σ y) = (σ (M.op y x)) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e69469
               have i₂ := b8e60904 x
               grind)
            | exact superpose b8e60904 b8e69469
            | exact resolve b8e69469 b8e60904
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60904 b8e69469
          have b8e69727 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e376
               have i₂ := b8e69470
               grind)
            | exact superpose b8e69470 b8e376
            | exact resolve b8e376 b8e69470
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e376 b8e69470
          have b8e69821 : (σ y) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e69727
               have r₂ := b8e24
               grind)
            | exact resolve b8e69727 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69727
          have b8e69848 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e61432 x
               have i₂ := b8e69821
               grind)
            | exact superpose b8e69821 b8e61432
            | exact resolve b8e61432 b8e69821
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61432 b8e69821
          have b8e69998 : False := by grind
          exact b8e69998

/-- `Equation1271`: `x = x ◇ (((y ◇ z) ◇ w) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_pxx_pyx_Equation1271 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1271 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1271.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e41 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
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
      have b0e42 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
      have b0e47 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b0e42 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e48 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
        intro X0
        first
        | (have j0 := b0e41 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e104 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 x X0
           have i₂ := b0e47 (σ X0)
           grind)
        | exact superpose b0e47 b0e17
        | exact resolve b0e17 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e106 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e104 X0
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e104
        | exact resolve b0e104 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e104
      have b0e565 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e106 y
           grind)
        | exact superpose b0e106 b0e18
        | (have r₁ := b0e18
           have r₂ := b0e106 y
           grind)
        | exact resolve b0e18 b0e106
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e106
      have b0e580 : False := by grind
      exact b0e580
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X1)) = X0 := by
          intro X0 X1 X2 X3
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e28 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X2 X0 X1 (M.op (M.op (M.op x x) x) x)
             have i₂ := b1e12 (M.op X0 X1) x x x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e28 X0 (M.op (M.op x x) x) X1
             have i₂ := b1e28 x x X0
             grind)
          | exact superpose b1e28 b1e28
          | exact resolve b1e28 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e40 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e15 (σ y) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | (have j0 := b1e15 (σ y) X0
             grind)
          | (have r₁ := b1e15 (σ y) x
             have r₂ := b1e22
             grind)
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e45 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have j0 := b1e40 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e56 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e33 (σ y) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e33
          | exact resolve b1e33 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e105 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 y X0
             have i₂ := b1e45 (σ X0)
             grind)
          | exact superpose b1e45 b1e18
          | exact resolve b1e18 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e115 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e56 (σ x)
             grind)
          | exact superpose b1e56 b1e19
          | exact resolve b1e19 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e366 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e56 (σ y)
             have i₂ := b1e105 y
             grind)
          | exact superpose b1e105 b1e56
          | exact resolve b1e56 b1e105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e105
        have b1e483 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e366
             grind)
          | exact superpose b1e366 b1e13
          | exact resolve b1e13 b1e366
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e366
        have b1e485 : y = (k y y) := by
          first
          | (have i₁ := b1e483
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e483
          | exact resolve b1e483 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e483
        have b1e593 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e17 y y
             have i₂ := b1e485
             grind)
          | exact superpose b1e485 b1e17
          | (have j0 := b1e17 y y
             grind)
          | exact resolve b1e17 b1e485
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e485
        have b1e594 : y = (M.op y y) := by grind
        clear b1e593
        have b1e651 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e33 y X0
             have i₂ := b1e594
             grind)
          | exact superpose b1e594 b1e33
          | exact resolve b1e33 b1e594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e594
        have b1e764 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e115
             have i₂ := b1e651 x
             grind)
          | exact superpose b1e651 b1e115
          | exact resolve b1e115 b1e651
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e115 b1e651
        have b1e767 : False := by grind
        exact b1e767
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e76 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e17 X2 X0
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X1
             have j1 := b2e17 X2 X2
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e84 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e76 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76
        have b2e739 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e84 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84
        have b2e740 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e739 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e739
        have b2e751 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e740 X0
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e740 X0
             have r₂ := b2e15 X0 x
             grind)
          | exact resolve b2e740 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e740
        have b2e758 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e751 (σ X0)
             grind)
          | exact superpose b2e751 b2e18
          | exact resolve b2e18 b2e751
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e765 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e758 X0
             have i₂ := b2e751 X0
             grind)
          | exact superpose b2e751 b2e758
          | exact resolve b2e758 b2e751
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e751 b2e758
        have b2e875 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e765 x
             grind)
          | exact superpose b2e765 b2e21
          | exact resolve b2e21 b2e765
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e765
        have b2e901 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e875
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e875
          | exact resolve b2e875 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e875
        have b2e902 : False := by grind
        exact b2e902
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X1)) = X0 := by
          intro X0 X1 X2 X3
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y y) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e28 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X2 X0 X1 (M.op (M.op (M.op x x) x) x)
             have i₂ := b3e12 (M.op X0 X1) x x x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e28 X0 (M.op (M.op x x) x) X1
             have i₂ := b3e28 x x X0
             grind)
          | exact superpose b3e28 b3e28
          | exact resolve b3e28 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e40 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
        have b3e45 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b3e40 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e47 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b3e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e47 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e55 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e33 y X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e33
          | exact resolve b3e33 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e56 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e33 (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e33
          | exact resolve b3e33 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e101 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 x X0
             have i₂ := b3e45 (σ X0)
             grind)
          | exact superpose b3e45 b3e18
          | exact resolve b3e18 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e407 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e101 y
             grind)
          | exact superpose b3e101 b3e19
          | exact resolve b3e19 b3e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e409 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e56 (σ x)
             have i₂ := b3e101 x
             grind)
          | exact superpose b3e101 b3e56
          | exact resolve b3e56 b3e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56 b3e101
        have b3e425 : (σ x) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e407
             have i₂ := b3e55 x
             grind)
          | exact superpose b3e55 b3e407
          | exact resolve b3e407 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55 b3e407
        have b3e523 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e425
             have i₂ := b3e54 x
             grind)
          | exact superpose b3e54 b3e425
          | (have j1 := b3e54 x
             grind)
          | exact resolve b3e425 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54 b3e425
        have b3e525 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have r₁ := b3e523
             have r₂ := b3e20
             grind)
          | exact resolve b3e523 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e523
        have b3e575 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e409
             have i₂ := b3e17 x x
             grind)
          | exact superpose b3e17 b3e409
          | (have j1 := b3e17 x x
             grind)
          | exact resolve b3e409 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e409
        have b3e580 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b3e575
        have b3e585 : x = (M.op x x) := by
          first
          | (have r₁ := b3e580
             have r₂ := b3e525
             grind)
          | exact resolve b3e580 b3e525
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e525 b3e580
        have b3e587 : False := by grind
        exact b3e587
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X1)) = X0 := by
            intro X0 X1 X2 X3
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e34 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X2 X0 X1 (M.op (M.op (M.op x x) x) x)
               have i₂ := b4e13 (M.op X0 X1) x x x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e34 X0 (M.op (M.op x x) x) X1
               have i₂ := b4e34 x x X0
               grind)
            | exact superpose b4e34 b4e34
            | exact resolve b4e34 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e61 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e39 y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e39
            | exact resolve b4e39 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e62 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e39 (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e39
            | exact resolve b4e39 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e124 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e62 (σ x)
               grind)
            | exact superpose b4e62 b4e20
            | exact resolve b4e20 b4e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62
          have b4e127 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e124
               have i₂ := b4e61 x
               grind)
            | exact superpose b4e61 b4e124
            | exact resolve b4e124 b4e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e61 b4e124
          have b4e128 : False := by grind
          exact b4e128
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e82 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 X0 X1
               have i₂ := b5e18 X2 X0
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X0 X1
               have j1 := b5e18 X2 X2
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X1 X1
               have r₂ := b5e18 X0 X1
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e91 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e82 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e82
          have b5e665 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e91 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e91
          have b5e666 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e665 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e665
          have b5e677 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e666 X0
               have j1 := b5e16 X0 X0
               grind)
            | (have r₁ := b5e666 X0
               have r₂ := b5e16 X0 x
               grind)
            | exact resolve b5e666 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e666
          have b5e684 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e677 (σ X0)
               grind)
            | exact superpose b5e677 b5e19
            | exact resolve b5e19 b5e677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e691 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e684 X0
               have i₂ := b5e677 X0
               grind)
            | exact superpose b5e677 b5e684
            | exact resolve b5e684 b5e677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e677 b5e684
          have b5e800 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e691 y
               grind)
            | exact superpose b5e691 b5e24
            | exact resolve b5e24 b5e691
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e691
          have b5e824 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e800
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e800
            | exact resolve b5e800 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e800
          have b5e825 : False := by grind
          exact b5e825
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X1)) = X0 := by
          intro X0 X1 X2 X3
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e27 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X2 X0 X1 (M.op (M.op (M.op x x) x) x)
             have i₂ := b6e12 (M.op X0 X1) x x x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e31 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e27 X0 (M.op (M.op x x) x) X1
             have i₂ := b6e27 x x X0
             grind)
          | exact superpose b6e27 b6e27
          | exact resolve b6e27 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e37 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
        have b6e42 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b6e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e43 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e31 (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e31
          | exact resolve b6e31 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e110 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e42 (σ X0)
             grind)
          | exact superpose b6e42 b6e18
          | exact resolve b6e18 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e194 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e43 (σ x)
             have i₂ := b6e110 x
             grind)
          | exact superpose b6e110 b6e43
          | exact resolve b6e43 b6e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43 b6e110
        have b6e276 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e194
             grind)
          | exact superpose b6e194 b6e13
          | exact resolve b6e13 b6e194
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e194
        have b6e278 : x = (k x x) := by
          first
          | (have i₁ := b6e276
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e276
          | exact resolve b6e276 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e276
        have b6e358 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e278
             grind)
          | exact superpose b6e278 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e278
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e278
        have b6e359 : x = (M.op x x) := by grind
        clear b6e358
        have b6e361 : False := by grind
        exact b6e361
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X1)) = X0 := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e33 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 X0 X1 (M.op (M.op (M.op x x) x) x)
               have i₂ := b7e13 (M.op X0 X1) x x x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e33 X0 (M.op (M.op x x) x) X1
               have i₂ := b7e33 x x X0
               grind)
            | exact superpose b7e33 b7e33
            | exact resolve b7e33 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e43 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e16 (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 (σ y) X0
               grind)
            | (have r₁ := b7e16 (σ y) x
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e48 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b7e43 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e49 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e37 (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e37
            | exact resolve b7e37 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e104 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 y X0
               have i₂ := b7e48 (σ X0)
               grind)
            | exact superpose b7e48 b7e19
            | exact resolve b7e19 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e230 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e49 (σ y)
               have i₂ := b7e104 y
               grind)
            | exact superpose b7e104 b7e49
            | exact resolve b7e49 b7e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49 b7e104
          have b7e266 : (τ (σ y)) = (k y y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e230
               grind)
            | exact superpose b7e230 b7e14
            | exact resolve b7e14 b7e230
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e230
          have b7e268 : y = (k y y) := by
            first
            | (have i₁ := b7e266
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e266
            | exact resolve b7e266 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e266
          have b7e349 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e268
               grind)
            | exact superpose b7e268 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e268
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e268
          have b7e350 : y = (M.op y y) := by grind
          clear b7e349
          have b7e352 : False := by grind
          exact b7e352
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e98 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ x)
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) x
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 X0 (σ x)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e103 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b8e98 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98
          have b8e151 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 x
               have i₂ := b8e103 (σ X0)
               grind)
            | exact superpose b8e103 b8e19
            | (have j1 := b8e103 (σ X0)
               grind)
            | exact resolve b8e19 b8e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e103
          have b8e5852 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e151 y
               grind)
            | exact superpose b8e151 b8e24
            | (have j1 := b8e151 y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e151 y
               grind)
            | exact resolve b8e24 b8e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e151
          have b8e5895 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
          clear b8e5852
          have b8e5983 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e5895
               grind)
            | exact superpose b8e5895 b8e20
            | exact resolve b8e20 b8e5895
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5895
          have b8e6190 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e5983
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e5983
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e5983 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5983
          have b8e6203 : y = (M.op y y) ∨ x = (M.op x x) := by grind
          clear b8e6190
          have b8e6210 : x = (M.op x x) := by
            first
            | (have r₁ := b8e6203
               have r₂ := b8e22
               grind)
            | exact resolve b8e6203 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6203
          have b8e6211 : False := by grind
          exact b8e6211
