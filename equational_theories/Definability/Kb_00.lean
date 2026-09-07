import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1738`: `x = (y ◇ y) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pxx_pxy_Equation1738 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1738 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1738.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
    · rcases eq_or_ne (M.op (k x y) x) ((k x y)) with h2a | h2a
      · have b0e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e18 : x = (M.op x y) := by grind
        have b0e19 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b0e21 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e17
          | exact resolve b0e17 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e22 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b0e21
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e21
          | exact resolve b0e21 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e21
        have b0e23 : False := by grind
        exact b0e23
      · have b1e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e18 : x = (M.op x y) := by grind
        have b1e19 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b1e21 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e17
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e17
          | exact resolve b1e17 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e22 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e21
          | exact resolve b1e21 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e21
        have b1e23 : False := by grind
        exact b1e23
    · rcases eq_or_ne (M.op (k x y) x) ((k x y)) with h2a | h2a
      · have b2e11 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X0)) = X0 := by
          intro X0 X1 X2
          grind
        have b2e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e18 : x = (M.op x y) := by grind
        have b2e19 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (k x y) = (M.op (k x y) x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b2e28 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b2e11 y X0 x
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e11
          | exact resolve b2e11 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (k x y) x)) := by
          intro X0
          first
          | (have i₁ := b2e11 x X0 (k x y)
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e11
          | exact resolve b2e11 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X1) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e11 (M.op (M.op X2 X0) X0) X1 (M.op (M.op X2 X0) X0)
             have i₂ := b2e11 X0 (M.op (M.op X2 X0) X0) X2
             grind)
          | exact superpose b2e11 b2e11
          | exact resolve b2e11 b2e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 : G, x = (M.op (M.op X0 X0) (k x y)) := by
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
        have b2e33 : ∀ X0 : G, y = (M.op (M.op X0 X0) x) := by
          intro X0
          first
          | (have i₁ := b2e28 X0
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e28
          | exact resolve b2e28 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e36 : x ≠ x ∨ (k x y) = (M.op x x) := by
          first
          | (have i₁ := b2e14 x y
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e14
          | (have j0 := b2e14 x y
             grind)
          | (have r₁ := b2e14 x y
             have r₂ := b2e18
             grind)
          | exact resolve b2e14 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : (k x y) = (M.op x x) := by grind
        clear b2e36
        have b2e42 : (M.op x x) = (M.op (M.op x x) x) := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e41
             grind)
          | exact superpose b2e41 b2e20
          | exact resolve b2e20 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e43 : y = (M.op x x) := by
          first
          | (have i₁ := b2e42
             have i₂ := b2e33 x
             grind)
          | exact superpose b2e33 b2e42
          | exact resolve b2e42 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42
        have b2e46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X0 X1
             have i₂ := b2e15 (σ X0) (σ X1)
             grind)
          | exact superpose b2e15 b2e16
          | (have j1 := b2e15 (σ X0) (σ X1)
             grind)
          | exact resolve b2e16 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e54 : x = (M.op y (k x y)) := by
          first
          | (have i₁ := b2e32 x
             have i₂ := b2e43
             grind)
          | exact superpose b2e43 b2e32
          | exact resolve b2e32 b2e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : ∀ X0 : G, (k x y) = (M.op (M.op X0 X0) x) := by
          intro X0
          first
          | (have i₁ := b2e11 (k x y) X0 (k x y)
             have i₂ := b2e32 (k x y)
             grind)
          | exact superpose b2e32 b2e11
          | exact resolve b2e11 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e62 : y = (k x y) := by
          first
          | (have i₁ := b2e57 x
             have i₂ := b2e33 x
             grind)
          | exact superpose b2e33 b2e57
          | exact resolve b2e57 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33 b2e57
        have b2e64 : x = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b2e54
             have i₂ := b2e41
             grind)
          | exact superpose b2e41 b2e54
          | exact resolve b2e54 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41 b2e54
        have b2e67 : x = (M.op y y) := by
          first
          | (have i₁ := b2e64
             have i₂ := b2e43
             grind)
          | exact superpose b2e43 b2e64
          | exact resolve b2e64 b2e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e43 b2e64
        have b2e101 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e31 X1 X3 x
             have i₂ := b2e31 X1 X0 x
             grind)
          | (have i₁ := b2e31 X0 X1 X0
             have i₂ := b2e31 X0 X0 x
             grind)
          | exact superpose b2e31 b2e31
          | exact resolve b2e31 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e136 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e31 X1 y X0
             have i₂ := b2e67
             grind)
          | exact superpose b2e67 b2e31
          | exact resolve b2e31 b2e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e289 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) (σ X1)) = (M.op (M.op X2 X2) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e31 (σ X1) X2 (σ X0)
             have i₂ := b2e46 X0 X1
             grind)
          | exact superpose b2e46 b2e31
          | (have j1 := b2e46 X0 X1
             grind)
          | exact resolve b2e31 b2e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e292 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e46 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e479 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e101 X0 X1 y
             have i₂ := b2e67
             grind)
          | exact superpose b2e67 b2e101
          | exact resolve b2e101 b2e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e101
        have b2e1976 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e292 x y
             have i₂ := b2e62
             grind)
          | exact superpose b2e62 b2e292
          | (have j0 := b2e292 x y
             grind)
          | exact resolve b2e292 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e292
        have b2e1984 : (σ x) ≠ (σ y) := by
          first
          | (have r₁ := b2e1976
             have r₂ := b2e19
             grind)
          | exact resolve b2e1976 b2e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1976
        have b2e3975 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e289 x y X0
             have i₂ := b2e62
             grind)
          | exact superpose b2e62 b2e289
          | (have j0 := b2e289 x y x
             grind)
          | exact resolve b2e289 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62 b2e289
        have b2e4086 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 X0) (σ y)) := by
          intro X0
          first
          | (have j0 := b2e3975 X0
             grind)
          | (have r₁ := b2e3975 X0
             have r₂ := b2e19
             grind)
          | exact resolve b2e3975 b2e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3975
        have b2e4112 : (M.op (σ y) (σ y)) = (M.op x (σ y)) := by
          first
          | (have i₁ := b2e4086 x
             have i₂ := b2e479 x (σ y)
             grind)
          | exact superpose b2e479 b2e4086
          | exact resolve b2e4086 b2e479
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e479 b2e4086
        have b2e4124 : (M.op x (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op x (σ y)) := by
          first
          | (have i₁ := b2e46 y y
             have i₂ := b2e4112
             grind)
          | exact superpose b2e4112 b2e46
          | exact resolve b2e46 b2e4112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46
        have b2e4154 : (σ y) ≠ (M.op x (σ y)) ∨ (M.op x (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b2e14 (σ y) (σ y)
             have i₂ := b2e4112
             grind)
          | exact superpose b2e4112 b2e14
          | exact resolve b2e14 b2e4112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4112
        have b2e4164 : (M.op x (σ y)) = (σ (k y y)) ∨ (σ y) ≠ (M.op x (σ y)) := by
          first
          | (have i₁ := b2e4154
             have i₂ := b2e16 y y
             grind)
          | exact superpose b2e16 b2e4154
          | exact resolve b2e4154 b2e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4154
        have b2e4191 : (M.op x (σ y)) = (σ (k y y)) := by
          first
          | (have r₁ := b2e4164
             have r₂ := b2e4124
             grind)
          | exact resolve b2e4164 b2e4124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4124 b2e4164
        have b2e4561 : (M.op x (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e4191
             have i₂ := b2e15 y y
             grind)
          | exact superpose b2e15 b2e4191
          | (have j1 := b2e15 y y
             grind)
          | exact resolve b2e4191 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4191
        have b2e4596 : (σ x) = (M.op x (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e4561
             have i₂ := b2e67
             grind)
          | exact superpose b2e67 b2e4561
          | exact resolve b2e4561 b2e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4561
        have b2e4599 : (σ x) = (M.op x (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e4596
             have i₂ := b2e67
             grind)
          | exact superpose b2e67 b2e4596
          | exact resolve b2e4596 b2e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67 b2e4596
        have b2e5049 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e136 x (σ y)
             have i₂ := b2e4599
             grind)
          | exact superpose b2e4599 b2e136
          | exact resolve b2e136 b2e4599
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e136 b2e4599
        have b2e5050 : x = y := by
          first
          | (have r₁ := b2e5049
             have r₂ := b2e19
             grind)
          | exact resolve b2e5049 b2e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5049
        have b2e5178 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e1984
             have i₂ := b2e5050
             grind)
          | exact superpose b2e5050 b2e1984
          | exact resolve b2e1984 b2e5050
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1984 b2e5050
        have b2e5184 : False := by grind
        exact b2e5184
      · have b3e11 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X0)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e18 : x = (M.op x y) := by grind
        have b3e19 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (k x y) ≠ (M.op (k x y) x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b3e22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 (τ X0) X1
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e16
          | exact resolve b3e16 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X1 (τ X0)
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e16
          | exact resolve b3e16 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (k (τ X0) X1)
             have i₂ := b3e22 X0 X1
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e22
        have b3e28 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b3e11 y X0 x
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e11
          | exact resolve b3e11 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X1) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e11 (M.op (M.op X2 X0) X0) X1 (M.op (M.op X2 X0) X0)
             have i₂ := b3e11 X0 (M.op (M.op X2 X0) X0) X2
             grind)
          | exact superpose b3e11 b3e11
          | exact resolve b3e11 b3e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : ∀ X0 : G, y = (M.op (M.op X0 X0) x) := by
          intro X0
          first
          | (have i₁ := b3e28 X0
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e28
          | exact resolve b3e28 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e32 : ∀ X0 : G, x = (M.op (M.op X0 X0) y) := by
          intro X0
          first
          | (have i₁ := b3e11 x X0 x
             have i₂ := b3e31 x
             grind)
          | exact superpose b3e31 b3e11
          | exact resolve b3e11 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : x ≠ x ∨ (k x y) = (M.op x x) := by
          first
          | (have i₁ := b3e14 x y
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e14
          | (have j0 := b3e14 x y
             grind)
          | (have r₁ := b3e14 x y
             have r₂ := b3e18
             grind)
          | exact resolve b3e14 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e37 : (k x y) = (M.op x x) := by grind
        clear b3e34
        have b3e38 : (M.op x x) ≠ (M.op (M.op x x) x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e37
             grind)
          | exact superpose b3e37 b3e20
          | exact resolve b3e20 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : y ≠ (M.op x x) := by
          first
          | (have i₁ := b3e38
             have i₂ := b3e31 x
             grind)
          | exact superpose b3e31 b3e38
          | exact resolve b3e38 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X0 X1
             have i₂ := b3e15 (σ X0) (σ X1)
             grind)
          | exact superpose b3e15 b3e16
          | (have j1 := b3e15 (σ X0) (σ X1)
             grind)
          | exact resolve b3e16 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e47 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e23 X1 X0
             have i₂ := b3e15 X0 (τ X1)
             grind)
          | exact superpose b3e15 b3e23
          | (have j1 := b3e15 X0 (τ X1)
             grind)
          | exact resolve b3e23 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23
        have b3e61 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
          intro X0 X2 X3
          first
          | (have i₁ := b3e30 (M.op (M.op X2 X0) X0) X3 (M.op x x)
             have i₂ := b3e11 X0 x X2
             grind)
          | exact superpose b3e11 b3e30
          | exact resolve b3e30 b3e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e69 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e30 X1 X3 x
             have i₂ := b3e30 X1 X0 x
             grind)
          | (have i₁ := b3e30 X0 X1 X0
             have i₂ := b3e30 X0 X0 x
             grind)
          | exact superpose b3e30 b3e30
          | exact resolve b3e30 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e75 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e11 X1 X2 x
             have i₂ := b3e30 X1 X0 x
             grind)
          | (have i₁ := b3e11 X0 X1 X0
             have i₂ := b3e30 X0 X0 X2
             grind)
          | exact superpose b3e30 b3e11
          | exact resolve b3e11 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e89 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X0)) = X0 := by
          intro X0 X2
          first
          | (have i₁ := b3e61 X0 X2 x
             have i₂ := b3e11 X0 x X2
             grind)
          | exact superpose b3e11 b3e61
          | exact resolve b3e61 b3e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61
        have b3e167 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) (σ X1)) = (M.op (M.op X2 X2) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e30 (σ X1) X2 (σ X0)
             have i₂ := b3e42 X0 X1
             grind)
          | exact superpose b3e42 b3e30
          | (have j1 := b3e42 X0 X1
             grind)
          | exact resolve b3e30 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e170 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e42 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e240 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e89 X1 x
             have i₂ := b3e30 X1 X0 x
             grind)
          | (have i₁ := b3e89 X0 X0
             have i₂ := b3e30 X0 X0 x
             grind)
          | exact superpose b3e30 b3e89
          | exact resolve b3e89 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e246 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op (M.op X1 X0) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e14 X0 (M.op (M.op X1 X0) X0)
             have i₂ := b3e89 X0 X1
             grind)
          | exact superpose b3e89 b3e14
          | (have j0 := b3e14 X0 (M.op (M.op X1 X0) X0)
             grind)
          | (have r₁ := b3e14 X0 (M.op (M.op x X0) X0)
             have r₂ := b3e89 X0 x
             grind)
          | exact resolve b3e14 b3e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e89
        have b3e248 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op (M.op X1 X0) X0)) := by
          intro X0 X1
          first
          | (have j0 := b3e246 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e246
        have b3e264 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e27 X1 (τ X0)
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e27
          | exact resolve b3e27 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e267 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e27 X0 X1
             have i₂ := b3e15 X0 (σ X1)
             grind)
          | exact superpose b3e15 b3e27
          | (have j1 := b3e15 X0 (σ X1)
             grind)
          | exact resolve b3e27 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e339 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e69 X2 X3 (M.op X1 X1)
             have i₂ := b3e69 X1 (M.op X1 X1) X0
             grind)
          | (have i₁ := b3e69 X2 X3 (M.op X1 X1)
             have i₂ := b3e69 X0 (M.op X1 X1) X1
             grind)
          | exact superpose b3e69 b3e69
          | exact resolve b3e69 b3e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e402 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) y) := by
          intro X0 X1
          first
          | (have i₁ := b3e32 (M.op X1 X1)
             have i₂ := b3e69 X1 (M.op X1 X1) X0
             grind)
          | (have i₁ := b3e32 (M.op X1 X1)
             have i₂ := b3e69 X0 (M.op X1 X1) X1
             grind)
          | exact superpose b3e69 b3e32
          | exact resolve b3e32 b3e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e405 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e240 (M.op X1 X1) X2
             have i₂ := b3e69 X1 (M.op X1 X1) X0
             grind)
          | (have i₁ := b3e240 (M.op X1 X1) X2
             have i₂ := b3e69 X0 (M.op X1 X1) X1
             grind)
          | exact superpose b3e69 b3e240
          | exact resolve b3e240 b3e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e564 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3)) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e75 (M.op X1 X1) X3 X2
             have i₂ := b3e69 X1 (M.op X1 X1) X0
             grind)
          | (have i₁ := b3e75 (M.op X1 X1) X3 X2
             have i₂ := b3e69 X0 (M.op X1 X1) X1
             grind)
          | exact superpose b3e69 b3e75
          | exact resolve b3e75 b3e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e645 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)) = (k (M.op (M.op X1 X0) X0) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e248 (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)
             have i₂ := b3e11 X0 (M.op (M.op X1 X0) X0) X1
             grind)
          | exact superpose b3e11 b3e248
          | exact resolve b3e248 b3e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e883 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X3 X3)) X2)) = X2 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e405 (M.op X1 X1) X3 X2
             have i₂ := b3e69 X1 (M.op X1 X1) X0
             grind)
          | (have i₁ := b3e405 (M.op X1 X1) X3 X2
             have i₂ := b3e69 X0 (M.op X1 X1) X1
             grind)
          | exact superpose b3e69 b3e405
          | exact resolve b3e405 b3e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1098 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e170 x y
             have i₂ := b3e37
             grind)
          | exact superpose b3e37 b3e170
          | (have j0 := b3e170 x y
             grind)
          | exact resolve b3e170 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e170
        have b3e1104 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have r₁ := b3e1098
             have r₂ := b3e19
             grind)
          | exact resolve b3e1098 b3e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1098
        have b3e1114 : ∀ X0 X1 X2 : G, (k (σ (M.op X2 X2)) X1) = (σ (M.op (M.op X0 X0) (τ X1))) ∨ (M.op X2 X2) = (M.op (M.op X0 X0) (τ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e47 (M.op X0 X0) X1
             have i₂ := b3e69 X0 (τ X1) x
             grind)
          | (have i₁ := b3e47 (M.op x x) X1
             have i₂ := b3e69 X0 (τ X1) x
             grind)
          | exact superpose b3e69 b3e47
          | exact resolve b3e47 b3e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47 b3e69
        have b3e2059 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (σ (M.op x x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e167 x y X0
             have i₂ := b3e37
             grind)
          | exact superpose b3e37 b3e167
          | (have j0 := b3e167 x y x
             grind)
          | exact resolve b3e167 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37 b3e167
        have b3e2140 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (σ (M.op x x)) (σ y)) := by
          intro X0
          first
          | (have j0 := b3e2059 X0
             grind)
          | (have r₁ := b3e2059 X0
             have r₂ := b3e19
             grind)
          | exact resolve b3e2059 b3e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2059
        have b3e2159 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (σ (k (M.op x x) y)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e2140 X0
             have i₂ := b3e42 (M.op x x) y
             grind)
          | exact superpose b3e42 b3e2140
          | (have j1 := b3e42 (M.op x x) y
             grind)
          | exact resolve b3e2140 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e2172 : ∀ X0 : G, (M.op (σ (M.op x x)) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e30 (σ y) x X0
             have i₂ := b3e2140 x
             grind)
          | exact superpose b3e2140 b3e30
          | exact resolve b3e30 b3e2140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2180 : (σ y) = (M.op (σ y) (M.op (σ (M.op x x)) (σ y))) := by
          first
          | (have i₁ := b3e405 x x (σ y)
             have i₂ := b3e2140 (M.op x x)
             grind)
          | exact superpose b3e2140 b3e405
          | exact resolve b3e405 b3e2140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e405 b3e2140
        have b3e2781 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2)) X4)) = X4 := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e75 (M.op X2 X2) X4 X3
             have i₂ := b3e339 X0 X1 X2 (M.op X2 X2)
             grind)
          | (have i₁ := b3e75 (M.op (M.op X0 X0) (M.op X1 X1)) X1 X2
             have i₂ := b3e339 X0 X1 X2 (M.op (M.op X0 X0) (M.op X1 X1))
             grind)
          | exact superpose b3e339 b3e75
          | exact resolve b3e75 b3e339
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e3905 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2)) (M.op X4 X4)) X5)) = X5 := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b3e564 (M.op X2 X2) X4 X3 X5
             have i₂ := b3e339 X0 X1 X2 (M.op X2 X2)
             grind)
          | (have i₁ := b3e564 (M.op (M.op X0 X0) (M.op X1 X1)) X1 X2 X3
             have i₂ := b3e339 X0 X1 X2 (M.op (M.op X0 X0) (M.op X1 X1))
             grind)
          | exact superpose b3e339 b3e564
          | exact resolve b3e564 b3e339
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e564
        have b3e4357 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e267 X0 (τ X0)
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e267
          | exact resolve b3e267 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e267
        have b3e4400 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e4357 X0 X1
             have i₂ := b3e264 X0 X1
             grind)
          | exact superpose b3e264 b3e4357
          | (have j0 := b3e4357 X0 X1
             grind)
          | exact resolve b3e4357 b3e264
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e264 b3e4357
        have b3e4405 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e4400 (σ X1) (σ X0)
             have i₂ := b3e16 X0 X1
             grind)
          | exact superpose b3e16 b3e4400
          | (have j0 := b3e4400 (σ X1) (σ X0)
             grind)
          | exact resolve b3e4400 b3e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4400
        have b3e4445 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e4405 X0 X1
             have i₂ := b3e12 (k X0 X1)
             grind)
          | exact superpose b3e12 b3e4405
          | (have j0 := b3e4405 X0 X1
             grind)
          | exact resolve b3e4405 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4405
        have b3e19926 : ∀ X0 X1 X2 : G, (k (τ (σ (M.op X2 X2))) X1) = (τ (σ (M.op (M.op X0 X0) (τ (σ X1))))) ∨ (M.op X2 X2) = (M.op (M.op X0 X0) (τ (σ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e27 (σ (M.op X2 X2)) X1
             have i₂ := b3e1114 X0 (σ X1) X2
             grind)
          | exact superpose b3e1114 b3e27
          | (have j1 := b3e1114 X0 (σ X1) X2
             grind)
          | exact resolve b3e27 b3e1114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e1114
        have b3e20034 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (τ (σ X1))) = (k (τ (σ (M.op X2 X2))) X1) ∨ (M.op X2 X2) = (M.op (M.op X0 X0) (τ (σ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e19926 X0 X1 X2
             have i₂ := b3e12 (M.op (M.op X0 X0) (τ (σ X1)))
             grind)
          | exact superpose b3e12 b3e19926
          | (have j0 := b3e19926 X0 X1 X2
             grind)
          | exact resolve b3e19926 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e19926
        have b3e20095 : ∀ X0 X1 X2 : G, (k (M.op X2 X2) X1) = (M.op (M.op X0 X0) (τ (σ X1))) ∨ (M.op X2 X2) = (M.op (M.op X0 X0) (τ (σ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e20034 X0 X1 X2
             have i₂ := b3e12 (M.op X2 X2)
             grind)
          | exact superpose b3e12 b3e20034
          | (have j0 := b3e20034 X0 X1 X2
             grind)
          | exact resolve b3e20034 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e20034
        have b3e20142 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k (M.op X2 X2) X1) ∨ (M.op X2 X2) = (M.op (M.op X0 X0) (τ (σ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e20095 X0 X1 X2
             have i₂ := b3e12 X1
             grind)
          | exact superpose b3e12 b3e20095
          | (have j0 := b3e20095 X0 X1 X2
             grind)
          | exact resolve b3e20095 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e20095
        have b3e20154 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k (M.op X2 X2) X1) ∨ (M.op X2 X2) = (M.op (M.op X0 X0) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e20142 X0 X1 X2
             have i₂ := b3e12 X1
             grind)
          | exact superpose b3e12 b3e20142
          | (have j0 := b3e20142 X0 X1 X2
             grind)
          | exact resolve b3e20142 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e20142
        have b3e33782 : ∀ X0 X1 X2 X3 : G, (M.op (k (M.op (M.op X0 X1) X1) X1) (M.op (M.op X2 X3) X3)) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e11 X3 (M.op (M.op X0 X1) X1) X2
             have i₂ := b3e645 X1 X0
             grind)
          | exact superpose b3e645 b3e11
          | exact resolve b3e11 b3e645
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33784 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (k (M.op (M.op X0 X1) X1) X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e30 X3 (M.op (M.op X0 X1) X1) X2
             have i₂ := b3e645 X1 X0
             grind)
          | exact superpose b3e645 b3e30
          | exact resolve b3e30 b3e645
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33785 : ∀ X0 X1 : G, y = (M.op (k (M.op (M.op X0 X1) X1) X1) x) := by
          intro X0 X1
          first
          | (have i₁ := b3e31 (M.op (M.op X0 X1) X1)
             have i₂ := b3e645 X1 X0
             grind)
          | exact superpose b3e645 b3e31
          | exact resolve b3e31 b3e645
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33786 : ∀ X0 X1 : G, x = (M.op (k (M.op (M.op X0 X1) X1) X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b3e32 (M.op (M.op X0 X1) X1)
             have i₂ := b3e645 X1 X0
             grind)
          | exact superpose b3e645 b3e32
          | exact resolve b3e32 b3e645
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e33815 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op X2 X2) (k (M.op (M.op X0 X1) X1) X1)) y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e402 X2 (M.op (M.op X0 X1) X1)
             have i₂ := b3e645 X1 X0
             grind)
          | exact superpose b3e645 b3e402
          | exact resolve b3e402 b3e645
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e402 b3e645
        have b3e34502 : ∀ X0 X1 : G, y = (M.op (k (M.op (M.op X0 X0) X1) X1) x) := by
          intro X0 X1
          first
          | (have i₁ := b3e33785 x X1
             have i₂ := b3e30 X1 X0 x
             grind)
          | (have i₁ := b3e33785 X0 X0
             have i₂ := b3e30 X0 X0 x
             grind)
          | exact superpose b3e30 b3e33785
          | exact resolve b3e33785 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33785
        have b3e35120 : x = (M.op (k (M.op (σ (M.op x x)) (σ y)) (σ y)) y) := by
          first
          | (have i₁ := b3e33786 x (σ y)
             have i₂ := b3e2172 x
             grind)
          | exact superpose b3e2172 b3e33786
          | exact resolve b3e33786 b3e2172
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33786
        have b3e35655 : ∀ X0 X1 X2 X3 : G, y = (M.op (k (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2)) X3) X3) x) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e34502 (M.op X2 X2) X3
             have i₂ := b3e339 X0 X1 X2 (M.op X2 X2)
             grind)
          | (have i₁ := b3e34502 (M.op (M.op X0 X0) (M.op X1 X1)) X1
             have i₂ := b3e339 X0 X1 X2 (M.op (M.op X0 X0) (M.op X1 X1))
             grind)
          | exact superpose b3e339 b3e34502
          | exact resolve b3e34502 b3e339
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e339 b3e34502
        have b3e38645 : ∀ X1 X2 : G, (M.op (k (M.op (σ (M.op x x)) (σ y)) (σ y)) (M.op (M.op X1 X2) X2)) = X2 := by
          intro X1 X2
          first
          | (have i₁ := b3e33782 x (σ y) X1 X2
             have i₂ := b3e2172 x
             grind)
          | exact superpose b3e2172 b3e33782
          | exact resolve b3e33782 b3e2172
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2172 b3e33782
        have b3e47283 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op X2 X2) (k (M.op (M.op X0 X0) X1) X1)) y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e33815 x X1 X2
             have i₂ := b3e30 X1 X0 x
             grind)
          | (have i₁ := b3e33815 X0 X0 X2
             have i₂ := b3e30 X0 X0 X2
             grind)
          | exact superpose b3e30 b3e33815
          | exact resolve b3e33815 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30 b3e33815
        have b3e51865 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (k (M.op (M.op X0 X1) X1) X1) (k (M.op (M.op X2 X2) X3) X3)) y) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e47283 X2 X3 (k (M.op (M.op X2 X2) X3) X3)
             have i₂ := b3e33784 X0 X1 (k (M.op (M.op X2 X2) X3) X3) (k (M.op (M.op X2 X2) X3) X3)
             grind)
          | exact superpose b3e33784 b3e47283
          | exact resolve b3e47283 b3e33784
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33784 b3e47283
        have b3e218008 : ∀ X0 X1 X2 : G, (M.op X1 (k (M.op X0 X0) X1)) = X1 ∨ (M.op X0 X0) = (M.op (M.op X2 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e240 X2 X1
             have i₂ := b3e20154 X2 X1 X0
             grind)
          | exact superpose b3e20154 b3e240
          | (have j1 := b3e20154 X2 X1 X0
             grind)
          | exact resolve b3e240 b3e20154
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e240 b3e20154
        have b3e223158 : ∀ X0 X1 X2 : G, y = (M.op (M.op (M.op X0 X0) X1) x) ∨ (M.op X1 (k (M.op X2 X2) X1)) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e31 X2
             have i₂ := b3e218008 X2 X1 X0
             grind)
          | (have i₁ := b3e31 (M.op X2 X2)
             have i₂ := b3e218008 X0 (M.op X2 X2) X2
             grind)
          | exact superpose b3e218008 b3e31
          | (have j1 := b3e218008 X2 X1 X2
             grind)
          | exact resolve b3e31 b3e218008
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e223330 : ∀ X0 X1 X3 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = X3 ∨ (M.op X3 (k (M.op X0 X0) X3)) = X3 := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e2781 x x (M.op x x) X1 X3
             have i₂ := b3e218008 X0 X3 (M.op (M.op x x) (M.op x x))
             grind)
          | (have i₁ := b3e2781 X0 X1 x X3 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op x x))
             have i₂ := b3e218008 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op x x)) X1 x
             grind)
          | exact superpose b3e218008 b3e2781
          | (have j1 := b3e218008 X0 X3 x
             grind)
          | exact resolve b3e2781 b3e218008
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2781 b3e218008
        have b3e237211 : ∀ X1 : G, y = (M.op x x) ∨ y = (M.op y (k (M.op X1 X1) y)) := by
          intro X1
          first
          | (have i₁ := b3e223158 (k (M.op (M.op x x) x) x) y X1
             have i₂ := b3e51865 x x x x
             grind)
          | exact superpose b3e51865 b3e223158
          | (have j0 := b3e223158 x y X1
             grind)
          | exact resolve b3e223158 b3e51865
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51865 b3e223158
        have b3e237572 : ∀ X1 : G, y = (M.op y (k (M.op X1 X1) y)) := by
          intro X1
          first
          | (have j0 := b3e237211 X1
             grind)
          | (have r₁ := b3e237211 X1
             have r₂ := b3e39
             grind)
          | exact resolve b3e237211 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e237211
        have b3e237735 : ∀ X0 : G, (k (M.op X0 X0) y) = (M.op (k (M.op (σ (M.op x x)) (σ y)) (σ y)) (M.op y (k (M.op X0 X0) y))) := by
          intro X0
          first
          | (have i₁ := b3e38645 y (k (M.op X0 X0) y)
             have i₂ := b3e237572 X0
             grind)
          | exact superpose b3e237572 b3e38645
          | exact resolve b3e38645 b3e237572
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38645
        have b3e237742 : ∀ X0 : G, (k (M.op X0 X0) y) = (M.op (k (M.op (σ (M.op x x)) (σ y)) (σ y)) y) := by
          intro X0
          first
          | (have i₁ := b3e237735 X0
             have i₂ := b3e237572 X0
             grind)
          | exact superpose b3e237572 b3e237735
          | exact resolve b3e237735 b3e237572
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e237572 b3e237735
        have b3e237797 : ∀ X0 : G, x = (k (M.op X0 X0) y) := by
          intro X0
          first
          | (have i₁ := b3e237742 X0
             have i₂ := b3e35120
             grind)
          | exact superpose b3e35120 b3e237742
          | exact resolve b3e237742 b3e35120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35120 b3e237742
        have b3e262235 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ (M.op x x))) ∨ (M.op (M.op X0 X0) (σ y)) = (σ (k (M.op x x) y)) := by
          intro X0
          first
          | (have i₁ := b3e2180
             have i₂ := b3e2159 X0
             grind)
          | exact superpose b3e2159 b3e2180
          | (have j1 := b3e2159 X0
             grind)
          | exact resolve b3e2180 b3e2159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2159 b3e2180
        have b3e262242 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x x))) := by
          intro X0
          first
          | (have i₁ := b3e262235 X0
             have i₂ := b3e237797 x
             grind)
          | exact superpose b3e237797 b3e262235
          | exact resolve b3e262235 b3e237797
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e262235
        have b3e282352 : ∀ X0 X2 : G, y = (M.op (k X0 (M.op X2 X2)) x) ∨ (M.op X0 (k (M.op X2 X2) X0)) = X0 := by
          intro X0 X2
          first
          | (have i₁ := b3e35655 x x (M.op x x) (M.op X2 X2)
             have i₂ := b3e223330 X2 (M.op (M.op x x) (M.op x x)) X0
             grind)
          | (have i₁ := b3e35655 X0 x X2 x
             have i₂ := b3e223330 X0 x (M.op (M.op (M.op (M.op X0 X0) (M.op x x)) (M.op X2 X2)) x)
             grind)
          | exact superpose b3e223330 b3e35655
          | (have j1 := b3e223330 X2 x X0
             grind)
          | exact resolve b3e35655 b3e223330
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35655 b3e223330
        have b3e329798 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ x)) ∨ (σ y) = (M.op (σ y) (σ (M.op x x))) := by
          intro X0
          first
          | (have i₁ := b3e3905 x x (M.op x x) X0 (M.op (M.op x x) (M.op x x)) (σ y)
             have i₂ := b3e262242 (M.op (M.op (M.op x x) (M.op x x)) (M.op (M.op x x) (M.op x x)))
             grind)
          | exact superpose b3e262242 b3e3905
          | exact resolve b3e3905 b3e262242
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3905 b3e262242
        have b3e330939 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x x))) := by
          first
          | (have i₁ := b3e883 x x (σ x) (M.op x x)
             have i₂ := b3e329798 (M.op (M.op x x) (M.op x x))
             grind)
          | exact superpose b3e329798 b3e883
          | exact resolve b3e883 b3e329798
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e883 b3e329798
        have b3e330958 : (σ y) = (M.op (σ y) (σ (M.op x x))) := by
          first
          | (have r₁ := b3e330939
             have r₂ := b3e19
             grind)
          | exact resolve b3e330939 b3e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e330939
        have b3e330998 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (k (σ (M.op x x)) (M.op (σ y) (σ (M.op x x)))) := by
          first
          | (have i₁ := b3e248 (σ (M.op x x)) (σ y)
             have i₂ := b3e330958
             grind)
          | exact superpose b3e330958 b3e248
          | exact resolve b3e248 b3e330958
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e248
        have b3e331068 : (k (σ (M.op x x)) (σ y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
          first
          | (have i₁ := b3e330998
             have i₂ := b3e330958
             grind)
          | exact superpose b3e330958 b3e330998
          | exact resolve b3e330998 b3e330958
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e330958 b3e330998
        have b3e331105 : (σ (k (M.op x x) y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
          first
          | (have i₁ := b3e331068
             have i₂ := b3e16 (M.op x x) y
             grind)
          | exact superpose b3e16 b3e331068
          | exact resolve b3e331068 b3e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e331068
        have b3e331134 : (σ x) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
          first
          | (have i₁ := b3e331105
             have i₂ := b3e237797 x
             grind)
          | exact superpose b3e237797 b3e331105
          | exact resolve b3e331105 b3e237797
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e237797 b3e331105
        have b3e352737 : (τ (σ x)) = (k (M.op x x) (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e4445 (M.op x x) (M.op x x)
             have i₂ := b3e331134
             grind)
          | exact superpose b3e331134 b3e4445
          | exact resolve b3e4445 b3e331134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4445 b3e331134
        have b3e354034 : (τ (σ x)) = (k (M.op x x) (M.op x x)) := by
          first
          | (have r₁ := b3e352737
             have r₂ := b3e1104
             grind)
          | exact resolve b3e352737 b3e1104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1104 b3e352737
        have b3e354276 : x = (k (M.op x x) (M.op x x)) := by
          first
          | (have i₁ := b3e354034
             have i₂ := b3e12 x
             grind)
          | exact superpose b3e12 b3e354034
          | exact resolve b3e354034 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e354034
        have b3e354489 : y = (M.op x x) ∨ (M.op x x) = (M.op (M.op x x) x) := by
          first
          | (have i₁ := b3e282352 (M.op x x) x
             have i₂ := b3e354276
             grind)
          | exact superpose b3e354276 b3e282352
          | exact resolve b3e282352 b3e354276
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e282352 b3e354276
        have b3e354696 : (M.op x x) = (M.op (M.op x x) x) := by
          first
          | (have r₁ := b3e354489
             have r₂ := b3e39
             grind)
          | exact resolve b3e354489 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e354489
        have b3e354773 : y = (M.op x x) := by
          first
          | (have i₁ := b3e354696
             have i₂ := b3e31 x
             grind)
          | exact superpose b3e31 b3e354696
          | exact resolve b3e354696 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31 b3e354696
        have b3e354804 : False := by grind
        exact b3e354804
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
    · rcases eq_or_ne (M.op (k x y) x) ((k x y)) with h2a | h2a
      · have b4e11 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X0)) = X0 := by
          intro X0 X1 X2
          grind
        have b4e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b4e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b4e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b4e15 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b4e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b4e18 : x ≠ (M.op x y) := by grind
        have b4e19 : (σ x) = (M.op (σ x) (σ y)) := by grind
        have b4e20 : (k x y) = (M.op (k x y) x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b4e22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b4e16 (τ X0) X1
             have i₂ := b4e13 X0
             grind)
          | exact superpose b4e13 b4e16
          | exact resolve b4e16 b4e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e24 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (σ y))) := by
          intro X0
          first
          | (have i₁ := b4e11 (σ y) X0 (σ x)
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e11
          | exact resolve b4e11 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e25 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (k x y) x)) := by
          intro X0
          first
          | (have i₁ := b4e11 x X0 (k x y)
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e11
          | exact resolve b4e11 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e27 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X1) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b4e11 (M.op (M.op X2 X0) X0) X1 (M.op (M.op X2 X0) X0)
             have i₂ := b4e11 X0 (M.op (M.op X2 X0) X0) X2
             grind)
          | exact superpose b4e11 b4e11
          | exact resolve b4e11 b4e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e28 : ∀ X0 : G, x = (M.op (M.op X0 X0) (k x y)) := by
          intro X0
          first
          | (have i₁ := b4e25 X0
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e25
          | exact resolve b4e25 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e25
        have b4e29 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b4e24 X0
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e24
          | exact resolve b4e24 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e24
        have b4e32 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b4e14 (σ x) (σ y)
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e14
          | (have j0 := b4e14 (σ x) (σ y)
             grind)
          | (have r₁ := b4e14 (σ x) (σ y)
             have r₂ := b4e19
             grind)
          | exact resolve b4e14 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e37 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b4e32
        have b4e38 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b4e37
             have i₂ := b4e16 x y
             grind)
          | exact superpose b4e16 b4e37
          | exact resolve b4e37 b4e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e37
        have b4e43 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op x y)) ∨ x = (M.op x y) := by
          intro X0
          first
          | (have i₁ := b4e28 X0
             have i₂ := b4e15 x y
             grind)
          | exact superpose b4e15 b4e28
          | (have j1 := b4e15 x y
             grind)
          | exact resolve b4e28 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e44 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b4e20
             have i₂ := b4e15 x y
             grind)
          | exact superpose b4e15 b4e20
          | (have j1 := b4e15 (M.op x y) x
             grind)
          | exact resolve b4e20 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b4e16 X0 X1
             have i₂ := b4e15 (σ X0) (σ X1)
             grind)
          | exact superpose b4e15 b4e16
          | (have j1 := b4e15 (σ X0) (σ X1)
             grind)
          | exact resolve b4e16 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e46 : (M.op x y) = (M.op (M.op x y) x) := by
          first
          | (have r₁ := b4e44
             have r₂ := b4e18
             grind)
          | exact resolve b4e44 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e44
        have b4e47 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op x y)) := by
          intro X0
          first
          | (have j0 := b4e43 X0
             grind)
          | (have r₁ := b4e43 X0
             have r₂ := b4e18
             grind)
          | exact resolve b4e43 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e43
        have b4e48 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
          first
          | (have i₁ := b4e14 (M.op x y) x
             have i₂ := b4e46
             grind)
          | exact superpose b4e46 b4e14
          | (have j0 := b4e14 (M.op x y) x
             grind)
          | (have r₁ := b4e14 (M.op x y) x
             have r₂ := b4e46
             grind)
          | exact resolve b4e14 b4e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e46
        have b4e50 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by grind
        clear b4e48
        have b4e76 : (σ y) = (M.op (σ (k x y)) (σ x)) := by
          first
          | (have i₁ := b4e29 (σ x)
             have i₂ := b4e38
             grind)
          | exact superpose b4e38 b4e29
          | exact resolve b4e29 b4e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e79 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b4e14 (σ x) (σ x)
             have i₂ := b4e38
             grind)
          | exact superpose b4e38 b4e14
          | exact resolve b4e14 b4e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e81 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b4e79
             have i₂ := b4e16 x x
             grind)
          | exact superpose b4e16 b4e79
          | exact resolve b4e79 b4e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e79
        have b4e83 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) x) := by
          intro X0
          first
          | (have i₁ := b4e11 (M.op x y) X0 (M.op x y)
             have i₂ := b4e47 (M.op x y)
             grind)
          | exact superpose b4e47 b4e11
          | exact resolve b4e11 b4e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e91 : ∀ X1 : G, (M.op (M.op X1 X1) (M.op x y)) = (M.op x (M.op x y)) := by
          intro X1
          first
          | (have i₁ := b4e27 (M.op x y) X1 (M.op x x)
             have i₂ := b4e47 x
             grind)
          | exact superpose b4e47 b4e27
          | exact resolve b4e27 b4e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e138 : x = (M.op x (M.op x y)) := by
          first
          | (have i₁ := b4e91 x
             have i₂ := b4e47 x
             grind)
          | exact superpose b4e47 b4e91
          | exact resolve b4e91 b4e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e47 b4e91
        have b4e252 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b4e45 x x
             have i₂ := b4e38
             grind)
          | exact superpose b4e38 b4e45
          | exact resolve b4e45 b4e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e259 : ∀ X0 : G, x = (M.op (σ (k X0 X0)) (k x y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b4e28 (σ X0)
             have i₂ := b4e45 X0 X0
             grind)
          | exact superpose b4e45 b4e28
          | (have j1 := b4e45 X0 X0
             grind)
          | exact resolve b4e28 b4e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e28
        have b4e265 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) (σ X1)) = (M.op (M.op X2 X2) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b4e27 (σ X1) X2 (σ X0)
             have i₂ := b4e45 X0 X1
             grind)
          | exact superpose b4e45 b4e27
          | (have j1 := b4e45 X0 X1
             grind)
          | exact resolve b4e27 b4e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e27 b4e45
        have b4e272 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have r₁ := b4e252
             have r₂ := b4e81
             grind)
          | exact resolve b4e252 b4e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e81 b4e252
        have b4e336 : (σ (M.op x y)) = (σ (k x x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b4e272
             have i₂ := b4e15 x y
             grind)
          | exact superpose b4e15 b4e272
          | (have j1 := b4e15 x y
             grind)
          | exact resolve b4e272 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e341 : (k x y) = (τ (σ (k x x))) := by
          first
          | (have i₁ := b4e12 (k x y)
             have i₂ := b4e272
             grind)
          | exact superpose b4e272 b4e12
          | exact resolve b4e12 b4e272
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e342 : (k x y) = (k x x) := by
          first
          | (have i₁ := b4e341
             have i₂ := b4e12 (k x x)
             grind)
          | exact superpose b4e12 b4e341
          | exact resolve b4e341 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e341
        have b4e345 : (σ (M.op x y)) = (σ (k x x)) := by
          first
          | (have r₁ := b4e336
             have r₂ := b4e18
             grind)
          | exact resolve b4e336 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e336
        have b4e362 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b4e15 x y
             have i₂ := b4e342
             grind)
          | exact superpose b4e342 b4e15
          | (have j0 := b4e15 x y
             grind)
          | exact resolve b4e15 b4e342
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e363 : (M.op x y) = (k x x) := by
          first
          | (have r₁ := b4e362
             have r₂ := b4e18
             grind)
          | exact resolve b4e362 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e362
        have b4e398 : (σ y) = (M.op (σ (k x x)) (σ x)) := by
          first
          | (have i₁ := b4e76
             have i₂ := b4e272
             grind)
          | exact superpose b4e272 b4e76
          | exact resolve b4e76 b4e272
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e76
        have b4e412 : (σ y) = (M.op (σ (M.op x y)) (σ x)) := by
          first
          | (have i₁ := b4e398
             have i₂ := b4e345
             grind)
          | exact superpose b4e345 b4e398
          | exact resolve b4e398 b4e345
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e398
        have b4e3754 : ∀ X0 : G, x = (M.op (k X0 (σ (τ X0))) (k x y)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b4e259 (τ X0)
             have i₂ := b4e22 X0 (τ X0)
             grind)
          | exact superpose b4e22 b4e259
          | (have j0 := b4e259 (τ X0)
             grind)
          | exact resolve b4e259 b4e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e22 b4e259
        have b4e3787 : ∀ X0 : G, x = (M.op (k X0 (σ (τ X0))) (k x x)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b4e3754 X0
             have i₂ := b4e342
             grind)
          | exact superpose b4e342 b4e3754
          | (have j0 := b4e3754 X0
             grind)
          | exact resolve b4e3754 b4e342
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e342 b4e3754
        have b4e3799 : ∀ X0 : G, x = (M.op (k X0 (σ (τ X0))) (M.op x y)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b4e3787 X0
             have i₂ := b4e363
             grind)
          | exact superpose b4e363 b4e3787
          | (have j0 := b4e3787 X0
             grind)
          | exact resolve b4e3787 b4e363
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e3787
        have b4e3806 : ∀ X0 : G, x = (M.op (k X0 X0) (M.op x y)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b4e3799 X0
             have i₂ := b4e13 X0
             grind)
          | exact superpose b4e13 b4e3799
          | (have j0 := b4e3799 X0
             grind)
          | exact resolve b4e3799 b4e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e3799
        have b4e3809 : ∀ X0 : G, x = (M.op (k X0 X0) (M.op x y)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b4e3806 X0
             have i₂ := b4e13 X0
             grind)
          | exact superpose b4e13 b4e3806
          | (have j0 := b4e3806 X0
             grind)
          | exact resolve b4e3806 b4e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e3806
        have b4e13289 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b4e3809 x
             have i₂ := b4e363
             grind)
          | exact superpose b4e363 b4e3809
          | (have j0 := b4e3809 x
             grind)
          | exact resolve b4e3809 b4e363
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e363 b4e3809
        have b4e13337 : x = (k (M.op x y) x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b4e13289
             have i₂ := b4e50
             grind)
          | exact superpose b4e50 b4e13289
          | exact resolve b4e13289 b4e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e50 b4e13289
        have b4e13362 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b4e265 (M.op x y) x X0
             have i₂ := b4e13337
             grind)
          | exact superpose b4e13337 b4e265
          | (have j0 := b4e265 (M.op x y) x x
             grind)
          | exact resolve b4e265 b4e13337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e265 b4e13337
        have b4e13371 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b4e13362 X0
             have i₂ := b4e38
             grind)
          | exact superpose b4e38 b4e13362
          | exact resolve b4e13362 b4e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e38 b4e13362
        have b4e13374 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (σ (k x x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b4e13371 X0
             have i₂ := b4e272
             grind)
          | exact superpose b4e272 b4e13371
          | exact resolve b4e13371 b4e272
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e272 b4e13371
        have b4e13377 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 X0) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b4e13374 X0
             have i₂ := b4e345
             grind)
          | exact superpose b4e345 b4e13374
          | exact resolve b4e13374 b4e345
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e345 b4e13374
        have b4e13380 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b4e13377 x
             have i₂ := b4e29 x
             grind)
          | exact superpose b4e29 b4e13377
          | exact resolve b4e13377 b4e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e29 b4e13377
        have b4e13382 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b4e13380
             have i₂ := b4e412
             grind)
          | exact superpose b4e412 b4e13380
          | exact resolve b4e13380 b4e412
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e412 b4e13380
        have b4e13383 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by grind
        clear b4e13382
        have b4e13926 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b4e12 (M.op x y)
             have i₂ := b4e13383
             grind)
          | exact superpose b4e13383 b4e12
          | exact resolve b4e12 b4e13383
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e13383
        have b4e13969 : y = (M.op x y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b4e13926
             have i₂ := b4e12 y
             grind)
          | exact superpose b4e12 b4e13926
          | exact resolve b4e13926 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e13926
        have b4e15499 : x = (M.op x y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b4e138
             have i₂ := b4e13969
             grind)
          | exact superpose b4e13969 b4e138
          | exact resolve b4e138 b4e13969
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e138 b4e13969
        have b4e15571 : x = (M.op x x) := by
          first
          | (have r₁ := b4e15499
             have r₂ := b4e18
             grind)
          | exact resolve b4e15499 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e15499
        have b4e16459 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b4e83 x
             have i₂ := b4e15571
             grind)
          | exact superpose b4e15571 b4e83
          | exact resolve b4e83 b4e15571
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e83
        have b4e16541 : x = (M.op x y) := by
          first
          | (have i₁ := b4e16459
             have i₂ := b4e15571
             grind)
          | exact superpose b4e15571 b4e16459
          | exact resolve b4e16459 b4e15571
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e15571 b4e16459
        have b4e16568 : False := by grind
        exact b4e16568
      · have b5e11 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X0)) = X0 := by
          intro X0 X1 X2
          grind
        have b5e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b5e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b5e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b5e15 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b5e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b5e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b5e18 : x ≠ (M.op x y) := by grind
        have b5e19 : (σ x) = (M.op (σ x) (σ y)) := by grind
        have b5e20 : (k x y) ≠ (M.op (k x y) x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b5e21 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b5e17
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e17
          | exact resolve b5e17 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b5e16 (τ X0) X1
             have i₂ := b5e13 X0
             grind)
          | exact superpose b5e13 b5e16
          | exact resolve b5e16 b5e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e24 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (σ y))) := by
          intro X0
          first
          | (have i₁ := b5e11 (σ y) X0 (σ x)
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e11
          | exact resolve b5e11 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e26 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X1) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b5e11 (M.op (M.op X2 X0) X0) X1 (M.op (M.op X2 X0) X0)
             have i₂ := b5e11 X0 (M.op (M.op X2 X0) X0) X2
             grind)
          | exact superpose b5e11 b5e11
          | exact resolve b5e11 b5e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e27 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b5e24 X0
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e24
          | exact resolve b5e24 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e24
        have b5e28 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b5e11 (σ x) X0 (σ x)
             have i₂ := b5e27 (σ x)
             grind)
          | exact superpose b5e27 b5e11
          | exact resolve b5e11 b5e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e30 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b5e14 (σ x) (σ y)
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e14
          | (have j0 := b5e14 (σ x) (σ y)
             grind)
          | (have r₁ := b5e14 (σ x) (σ y)
             have r₂ := b5e19
             grind)
          | exact resolve b5e14 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e33 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b5e30
        have b5e34 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b5e33
             have i₂ := b5e16 x y
             grind)
          | exact superpose b5e16 b5e33
          | exact resolve b5e33 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e33
        have b5e40 : (M.op x y) ≠ (M.op (M.op x y) x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b5e20
             have i₂ := b5e15 x y
             grind)
          | exact superpose b5e15 b5e20
          | (have j1 := b5e15 x y
             grind)
          | (have r₁ := b5e20
             have r₂ := b5e15 (k x y) x
             grind)
          | exact resolve b5e20 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b5e16 X0 X1
             have i₂ := b5e15 (σ X0) (σ X1)
             grind)
          | exact superpose b5e15 b5e16
          | (have j1 := b5e15 (σ X0) (σ X1)
             grind)
          | exact resolve b5e16 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e42 : (M.op x y) ≠ (M.op (M.op x y) x) := by
          first
          | (have r₁ := b5e40
             have r₂ := b5e18
             grind)
          | exact resolve b5e40 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e40
        have b5e47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b5e12 (k (τ X0) X1)
             have i₂ := b5e22 X0 X1
             grind)
          | exact superpose b5e22 b5e12
          | exact resolve b5e12 b5e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e57 : (σ x) = (M.op (σ (k x y)) (σ y)) := by
          first
          | (have i₁ := b5e28 (σ x)
             have i₂ := b5e34
             grind)
          | exact superpose b5e34 b5e28
          | exact resolve b5e28 b5e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e28
        have b5e58 : (σ y) = (M.op (σ (k x y)) (σ x)) := by
          first
          | (have i₁ := b5e27 (σ x)
             have i₂ := b5e34
             grind)
          | exact superpose b5e34 b5e27
          | exact resolve b5e27 b5e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e60 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b5e14 (σ x) (σ x)
             have i₂ := b5e34
             grind)
          | exact superpose b5e34 b5e14
          | exact resolve b5e14 b5e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e62 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b5e60
             have i₂ := b5e16 x x
             grind)
          | exact superpose b5e16 b5e60
          | exact resolve b5e60 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e60
        have b5e67 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b5e47 X0 X1
             have i₂ := b5e15 X0 (σ X1)
             grind)
          | exact superpose b5e15 b5e47
          | (have j1 := b5e15 X0 (σ X1)
             grind)
          | exact resolve b5e47 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e47
        have b5e74 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
          intro X0 X2 X3
          first
          | (have i₁ := b5e26 (M.op (M.op X2 X0) X0) X3 (M.op x x)
             have i₂ := b5e11 X0 x X2
             grind)
          | exact superpose b5e11 b5e26
          | exact resolve b5e26 b5e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e75 : ∀ X1 : G, (M.op (M.op X1 X1) (σ x)) = (M.op (σ y) (σ x)) := by
          intro X1
          first
          | (have i₁ := b5e26 (σ x) X1 (M.op x x)
             have i₂ := b5e27 x
             grind)
          | exact superpose b5e27 b5e26
          | exact resolve b5e26 b5e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e88 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X1) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b5e26 X1 x X0
             have i₂ := b5e26 X1 x X2
             grind)
          | (have i₁ := b5e26 X0 X0 X2
             have i₂ := b5e26 X0 X1 X0
             grind)
          | exact superpose b5e26 b5e26
          | exact resolve b5e26 b5e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e103 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b5e75 x
             have i₂ := b5e27 x
             grind)
          | exact superpose b5e27 b5e75
          | exact resolve b5e75 b5e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e27 b5e75
        have b5e104 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X0)) = X0 := by
          intro X0 X2
          first
          | (have i₁ := b5e74 X0 X2 x
             have i₂ := b5e11 X0 x X2
             grind)
          | exact superpose b5e11 b5e74
          | exact resolve b5e74 b5e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e74
        have b5e108 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b5e14 (σ y) (σ x)
             have i₂ := b5e103
             grind)
          | exact superpose b5e103 b5e14
          | (have j0 := b5e14 (σ y) (σ x)
             grind)
          | (have r₁ := b5e14 (σ y) (σ x)
             have r₂ := b5e103
             grind)
          | exact resolve b5e14 b5e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e103
        have b5e110 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b5e108
        have b5e111 : (M.op (σ y) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b5e110
             have i₂ := b5e16 y x
             grind)
          | exact superpose b5e16 b5e110
          | exact resolve b5e110 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e110
        have b5e174 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b5e104 X1 x
             have i₂ := b5e26 X1 X0 x
             grind)
          | (have i₁ := b5e104 X0 X0
             have i₂ := b5e26 X0 X0 x
             grind)
          | exact superpose b5e26 b5e104
          | exact resolve b5e104 b5e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e104
        have b5e198 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b5e41 x x
             have i₂ := b5e34
             grind)
          | exact superpose b5e34 b5e41
          | exact resolve b5e41 b5e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e34
        have b5e203 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (σ (k X0 X0)) X2) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b5e26 X2 (σ X0) X1
             have i₂ := b5e41 X0 X0
             grind)
          | exact superpose b5e41 b5e26
          | (have j1 := b5e41 X0 X0
             grind)
          | exact resolve b5e26 b5e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e26
        have b5e216 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have r₁ := b5e198
             have r₂ := b5e62
             grind)
          | exact resolve b5e198 b5e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e62 b5e198
        have b5e221 : (σ (M.op x y)) = (σ (k x x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b5e216
             have i₂ := b5e15 x y
             grind)
          | exact superpose b5e15 b5e216
          | (have j1 := b5e15 x y
             grind)
          | exact resolve b5e216 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e227 : (k x y) = (τ (σ (k x x))) := by
          first
          | (have i₁ := b5e12 (k x y)
             have i₂ := b5e216
             grind)
          | exact superpose b5e216 b5e12
          | exact resolve b5e12 b5e216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e228 : (k x y) = (k x x) := by
          first
          | (have i₁ := b5e227
             have i₂ := b5e12 (k x x)
             grind)
          | exact superpose b5e12 b5e227
          | exact resolve b5e227 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e227
        have b5e232 : (σ (M.op x y)) = (σ (k x x)) := by
          first
          | (have r₁ := b5e221
             have r₂ := b5e18
             grind)
          | exact resolve b5e221 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e221
        have b5e241 : (k x x) ≠ (M.op (k x x) x) := by
          first
          | (have i₁ := b5e20
             have i₂ := b5e228
             grind)
          | exact superpose b5e228 b5e20
          | exact resolve b5e20 b5e228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e242 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b5e15 x y
             have i₂ := b5e228
             grind)
          | exact superpose b5e228 b5e15
          | (have j0 := b5e15 x y
             grind)
          | exact resolve b5e15 b5e228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e243 : (M.op x y) = (k x x) := by
          first
          | (have r₁ := b5e242
             have r₂ := b5e18
             grind)
          | exact resolve b5e242 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e242
        have b5e266 : (σ y) = (M.op (σ (k x x)) (σ x)) := by
          first
          | (have i₁ := b5e58
             have i₂ := b5e216
             grind)
          | exact superpose b5e216 b5e58
          | exact resolve b5e58 b5e216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e58
        have b5e280 : (σ y) = (M.op (σ (M.op x y)) (σ x)) := by
          first
          | (have i₁ := b5e266
             have i₂ := b5e232
             grind)
          | exact superpose b5e232 b5e266
          | exact resolve b5e266 b5e232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e266
        have b5e450 : (M.op x x) ≠ (M.op (M.op x x) x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b5e241
             have i₂ := b5e15 x x
             grind)
          | exact superpose b5e15 b5e241
          | (have j1 := b5e15 x x
             grind)
          | (have r₁ := b5e241
             have r₂ := b5e15 (k x x) x
             grind)
          | exact resolve b5e241 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e241
        have b5e587 : (σ x) = (σ (k (k x y) y)) ∨ (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b5e41 (k x y) y
             have i₂ := b5e57
             grind)
          | exact superpose b5e57 b5e41
          | exact resolve b5e41 b5e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e57
        have b5e602 : (σ x) = (σ (k (k x x) y)) ∨ (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b5e587
             have i₂ := b5e228
             grind)
          | exact superpose b5e228 b5e587
          | exact resolve b5e587 b5e228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e228 b5e587
        have b5e608 : (σ x) = (σ (k (M.op x y) y)) ∨ (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b5e602
             have i₂ := b5e243
             grind)
          | exact superpose b5e243 b5e602
          | exact resolve b5e602 b5e243
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e602
        have b5e610 : (σ x) = (σ (k x x)) ∨ (σ x) = (σ (k (M.op x y) y)) := by
          first
          | (have i₁ := b5e608
             have i₂ := b5e216
             grind)
          | exact superpose b5e216 b5e608
          | exact resolve b5e608 b5e216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e216 b5e608
        have b5e612 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (k (M.op x y) y)) := by
          first
          | (have i₁ := b5e610
             have i₂ := b5e232
             grind)
          | exact superpose b5e232 b5e610
          | exact resolve b5e610 b5e232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e232 b5e610
        have b5e614 : (σ x) = (σ (k (M.op x y) y)) := by
          first
          | (have r₁ := b5e612
             have r₂ := b5e21
             grind)
          | exact resolve b5e612 b5e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e21 b5e612
        have b5e708 : (k (M.op x y) y) = (τ (σ x)) := by
          first
          | (have i₁ := b5e12 (k (M.op x y) y)
             have i₂ := b5e614
             grind)
          | exact superpose b5e614 b5e12
          | exact resolve b5e12 b5e614
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e614
        have b5e719 : x = (k (M.op x y) y) := by
          first
          | (have i₁ := b5e708
             have i₂ := b5e12 x
             grind)
          | exact superpose b5e12 b5e708
          | exact resolve b5e708 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e708
        have b5e1177 : (σ (k y x)) = (σ (k y y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b5e41 y y
             have i₂ := b5e111
             grind)
          | exact superpose b5e111 b5e41
          | exact resolve b5e41 b5e111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e41
        have b5e1193 : (σ y) ≠ (σ (k y x)) ∨ (σ (k y x)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b5e14 (σ y) (σ y)
             have i₂ := b5e111
             grind)
          | exact superpose b5e111 b5e14
          | exact resolve b5e14 b5e111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e111
        have b5e1207 : (σ (k y x)) = (σ (k y y)) ∨ (σ y) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b5e1193
             have i₂ := b5e16 y y
             grind)
          | exact superpose b5e16 b5e1193
          | exact resolve b5e1193 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1193
        have b5e1213 : (σ (k y x)) = (σ (k y y)) := by
          first
          | (have r₁ := b5e1207
             have r₂ := b5e1177
             grind)
          | exact resolve b5e1207 b5e1177
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1177 b5e1207
        have b5e1247 : (k y y) = (τ (σ (k y x))) := by
          first
          | (have i₁ := b5e12 (k y y)
             have i₂ := b5e1213
             grind)
          | exact superpose b5e1213 b5e12
          | exact resolve b5e12 b5e1213
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1213
        have b5e1262 : (k y x) = (k y y) := by
          first
          | (have i₁ := b5e1247
             have i₂ := b5e12 (k y x)
             grind)
          | exact superpose b5e12 b5e1247
          | exact resolve b5e1247 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1247
        have b5e2504 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (k X0 (σ (τ X0))) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b5e203 (τ X0) X1 X2
             have i₂ := b5e22 X0 (τ X0)
             grind)
          | exact superpose b5e22 b5e203
          | (have j0 := b5e203 (τ X0) X1 X2
             grind)
          | exact resolve b5e203 b5e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e22 b5e203
        have b5e2581 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (k X0 X0) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b5e2504 X0 X1 X2
             have i₂ := b5e13 X0
             grind)
          | exact superpose b5e13 b5e2504
          | (have j0 := b5e2504 X0 X1 X2
             grind)
          | exact resolve b5e2504 b5e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e2504
        have b5e2619 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (k X0 X0) X2) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b5e2581 X0 X1 X2
             have i₂ := b5e13 X0
             grind)
          | exact superpose b5e13 b5e2581
          | (have j0 := b5e2581 X0 X1 X2
             grind)
          | exact resolve b5e2581 b5e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e2581
        have b5e10127 : (τ (σ y)) = (k (τ (σ (M.op x y))) x) ∨ (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b5e67 (σ (M.op x y)) x
             have i₂ := b5e280
             grind)
          | exact superpose b5e280 b5e67
          | exact resolve b5e67 b5e280
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e67 b5e280
        have b5e10178 : (k (M.op x y) x) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b5e10127
             have i₂ := b5e12 (M.op x y)
             grind)
          | exact superpose b5e12 b5e10127
          | exact resolve b5e10127 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e10127
        have b5e10209 : y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b5e10178
             have i₂ := b5e12 y
             grind)
          | exact superpose b5e12 b5e10178
          | exact resolve b5e10178 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e10178
        have b5e10682 : ∀ X0 X1 : G, (M.op X1 (M.op (k X0 X0) X1)) = X1 ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b5e174 X1 X1
             have i₂ := b5e2619 X0 X1 X1
             grind)
          | exact superpose b5e2619 b5e174
          | (have j1 := b5e2619 X0 X1 x
             grind)
          | exact resolve b5e174 b5e2619
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e174 b5e2619
        have b5e13558 : y = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b5e15 (M.op x y) x
             have i₂ := b5e10209
             grind)
          | exact superpose b5e10209 b5e15
          | (have j0 := b5e15 (M.op x y) x
             grind)
          | exact resolve b5e15 b5e10209
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e10209
        have b5e13572 : y = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
          first
          | (have r₁ := b5e13558
             have r₂ := b5e42
             grind)
          | exact resolve b5e13558 b5e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e13558
        have b5e14117 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = X0 ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b5e10682 x X0
             have i₂ := b5e243
             grind)
          | exact superpose b5e243 b5e10682
          | (have j0 := b5e10682 x x
             grind)
          | exact resolve b5e10682 b5e243
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e10682
        have b5e14694 : ∀ X0 : G, (M.op x x) ≠ (M.op (M.op X0 x) x) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b5e450
             have i₂ := b5e88 x x X0
             grind)
          | (have i₁ := b5e450
             have i₂ := b5e88 X0 x x
             grind)
          | exact superpose b5e88 b5e450
          | exact resolve b5e450 b5e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e450
        have b5e16556 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b5e14117 x
             have i₂ := b5e13572
             grind)
          | exact superpose b5e13572 b5e14117
          | exact resolve b5e14117 b5e13572
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e13572 b5e14117
        have b5e16659 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b5e16556
             have r₂ := b5e18
             grind)
          | exact resolve b5e16556 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e16556
        have b5e16911 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b5e12 (M.op x y)
             have i₂ := b5e16659
             grind)
          | exact superpose b5e16659 b5e12
          | exact resolve b5e12 b5e16659
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e16659
        have b5e16961 : y = (M.op x y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b5e16911
             have i₂ := b5e12 y
             grind)
          | exact superpose b5e12 b5e16911
          | exact resolve b5e16911 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e16911
        have b5e17454 : y ≠ (M.op y x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b5e42
             have i₂ := b5e16961
             grind)
          | exact superpose b5e16961 b5e42
          | exact resolve b5e42 b5e16961
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e42
        have b5e17469 : x = (k y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b5e719
             have i₂ := b5e16961
             grind)
          | exact superpose b5e16961 b5e719
          | exact resolve b5e719 b5e16961
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e719 b5e16961
        have b5e17515 : x = (k y x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b5e17469
             have i₂ := b5e1262
             grind)
          | exact superpose b5e1262 b5e17469
          | exact resolve b5e17469 b5e1262
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1262 b5e17469
        have b5e18413 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b5e15 y x
             have i₂ := b5e17515
             grind)
          | exact superpose b5e17515 b5e15
          | (have j0 := b5e15 y x
             grind)
          | exact resolve b5e15 b5e17515
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e17515
        have b5e18426 : x = (M.op y x) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b5e18413
             have r₂ := b5e17454
             grind)
          | exact resolve b5e18413 b5e17454
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e17454 b5e18413
        have b5e19003 : ∀ X0 : G, (M.op x x) = (M.op (M.op X0 x) x) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b5e88 X0 x y
             have i₂ := b5e18426
             grind)
          | exact superpose b5e18426 b5e88
          | exact resolve b5e88 b5e18426
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e88 b5e18426
        have b5e19019 : x = (M.op x x) := by
          first
          | (have r₁ := b5e19003 x
             have r₂ := b5e14694 x
             grind)
          | exact resolve b5e19003 b5e14694
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e14694 b5e19003
        have b5e19369 : x ≠ x ∨ x = (k x x) := by
          first
          | (have i₁ := b5e14 x x
             have i₂ := b5e19019
             grind)
          | exact superpose b5e19019 b5e14
          | (have r₁ := b5e14 x x
             have r₂ := b5e19019
             grind)
          | exact resolve b5e14 b5e19019
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e19019
        have b5e19384 : x = (k x x) := by grind
        clear b5e19369
        have b5e19547 : x = (M.op x y) := by
          first
          | (have i₁ := b5e243
             have i₂ := b5e19384
             grind)
          | exact superpose b5e19384 b5e243
          | exact resolve b5e243 b5e19384
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e243 b5e19384
        have b5e19581 : False := by grind
        exact b5e19581
    · rcases eq_or_ne (M.op (k x y) x) ((k x y)) with h2a | h2a
      · have b6e11 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X0) X0)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e18 : x ≠ (M.op x y) := by grind
        have b6e19 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (k x y) = (M.op (k x y) x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b6e23 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (k x y) x)) := by
          intro X0
          first
          | (have i₁ := b6e11 x X0 (k x y)
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e11
          | exact resolve b6e11 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e26 : ∀ X0 : G, x = (M.op (M.op X0 X0) (k x y)) := by
          intro X0
          first
          | (have i₁ := b6e23 X0
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e23
          | exact resolve b6e23 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e27 : ∀ X0 : G, (k x y) = (M.op (M.op X0 X0) x) := by
          intro X0
          first
          | (have i₁ := b6e11 (k x y) X0 (k x y)
             have i₂ := b6e26 (k x y)
             grind)
          | exact superpose b6e26 b6e11
          | exact resolve b6e11 b6e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e38 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op x y)) ∨ x = (M.op x y) := by
          intro X0
          first
          | (have i₁ := b6e26 X0
             have i₂ := b6e15 x y
             grind)
          | exact superpose b6e15 b6e26
          | (have j1 := b6e15 x y
             grind)
          | exact resolve b6e26 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X0 X1
             have i₂ := b6e15 (σ X0) (σ X1)
             grind)
          | exact superpose b6e15 b6e16
          | (have j1 := b6e15 (σ X0) (σ X1)
             grind)
          | exact resolve b6e16 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e42 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op x y)) := by
          intro X0
          first
          | (have j0 := b6e38 X0
             grind)
          | (have r₁ := b6e38 X0
             have r₂ := b6e18
             grind)
          | exact resolve b6e38 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e52 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) x) := by
          intro X0
          first
          | (have i₁ := b6e11 (M.op x y) X0 (M.op x y)
             have i₂ := b6e42 (M.op x y)
             grind)
          | exact superpose b6e42 b6e11
          | exact resolve b6e11 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e65 : (M.op x y) = (k x y) := by
          first
          | (have i₁ := b6e27 x
             have i₂ := b6e52 x
             grind)
          | exact superpose b6e52 b6e27
          | exact resolve b6e27 b6e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27 b6e52
        have b6e261 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e17
             have i₂ := b6e40 x y
             grind)
          | exact superpose b6e40 b6e17
          | (have j1 := b6e40 x y
             grind)
          | exact resolve b6e17 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e280 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b6e261
             have r₂ := b6e19
             grind)
          | exact resolve b6e261 b6e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e261
        have b6e284 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b6e280
             have i₂ := b6e65
             grind)
          | exact superpose b6e65 b6e280
          | exact resolve b6e280 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65 b6e280
        have b6e285 : False := by grind
        exact b6e285
      · have b7e15 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b7e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b7e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b7e18 : x ≠ (M.op x y) := by grind
        have b7e19 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b7e40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e16 X0 X1
             have i₂ := b7e15 (σ X0) (σ X1)
             grind)
          | exact superpose b7e15 b7e16
          | (have j1 := b7e15 (σ X0) (σ X1)
             grind)
          | exact resolve b7e16 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e134 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e40 x y
             grind)
          | exact superpose b7e40 b7e17
          | (have j1 := b7e40 x y
             grind)
          | exact resolve b7e17 b7e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e40
        have b7e148 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b7e134
             have r₂ := b7e19
             grind)
          | exact resolve b7e134 b7e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e134
        have b7e152 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b7e148
             have i₂ := b7e15 x y
             grind)
          | exact superpose b7e15 b7e148
          | (have j1 := b7e15 x y
             grind)
          | exact resolve b7e148 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e148
        have b7e153 : x = (M.op x y) := by grind
        clear b7e152
        have b7e154 : False := by grind
        exact b7e154

/-- `Equation3737`: `x ◇ y = (x ◇ z) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_pxx_pyx_Equation3737 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3737 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3737.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
      · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e18 : y = (M.op y x) := by grind
        have b0e19 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b0e20 : x = (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b0e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e17
          | exact resolve b0e17 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e27 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b0e11 y X0 x
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e11
          | exact resolve b0e11 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e29 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ x)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b0e11 X0 (σ y) (σ x)
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e11
          | exact resolve b0e11 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e31 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 x) y) := by
          intro X0
          first
          | (have i₁ := b0e11 X0 y x
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e11
          | exact resolve b0e11 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e37 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e14 (σ x) (σ y)
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e14
          | (have j0 := b0e14 (σ x) (σ y)
             grind)
          | (have r₁ := b0e14 (σ x) (σ y)
             have r₂ := b0e19
             grind)
          | exact resolve b0e14 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e38 : x ≠ x ∨ (k y x) = (M.op y y) := by
          first
          | (have i₁ := b0e14 y x
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e14
          | (have j0 := b0e14 y x
             grind)
          | (have r₁ := b0e14 y x
             have r₂ := b0e20
             grind)
          | exact resolve b0e14 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e40 : y ≠ y ∨ (M.op x x) = (k x y) := by
          first
          | (have i₁ := b0e14 x y
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e14
          | (have j0 := b0e14 x y
             grind)
          | (have r₁ := b0e14 x y
             have r₂ := b0e18
             grind)
          | exact resolve b0e14 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e41 : (M.op x x) = (k x y) := by grind
        clear b0e40
        have b0e42 : (k y x) = (M.op y y) := by grind
        clear b0e38
        have b0e43 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b0e37
        have b0e45 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b0e43
             have i₂ := b0e16 x y
             grind)
          | exact superpose b0e16 b0e43
          | exact resolve b0e43 b0e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e43
        have b0e47 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b0e45
             have i₂ := b0e41
             grind)
          | exact superpose b0e41 b0e45
          | exact resolve b0e45 b0e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41 b0e45
        have b0e50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e16 X1 X0
             have i₂ := b0e15 (σ X1) (σ X0)
             grind)
          | exact superpose b0e15 b0e16
          | (have j1 := b0e15 (σ X1) (σ X0)
             grind)
          | exact resolve b0e16 b0e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e70 : ∀ X0 : G, (M.op X0 y) ≠ (M.op X0 x) ∨ (M.op y y) = (k y (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b0e14 y (M.op X0 x)
             have i₂ := b0e31 X0
             grind)
          | exact superpose b0e31 b0e14
          | (have j0 := b0e14 y (M.op X0 x)
             grind)
          | exact resolve b0e14 b0e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e144 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x x)) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b0e11 (σ x) X0 (σ x)
             have i₂ := b0e47
             grind)
          | exact superpose b0e47 b0e11
          | exact resolve b0e11 b0e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e190 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b0e14 (σ y) (M.op X0 (σ x))
             have i₂ := b0e29 X0
             grind)
          | exact superpose b0e29 b0e14
          | (have j0 := b0e14 (σ y) (M.op X0 (σ x))
             grind)
          | exact resolve b0e14 b0e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e29
        have b0e604 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ (k X0 X1)) (M.op X2 (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e11 (σ X1) X2 (σ X0)
             have i₂ := b0e50 X1 X0
             grind)
          | exact superpose b0e50 b0e11
          | (have j1 := b0e50 X1 X0
             grind)
          | exact resolve b0e11 b0e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e50
        have b0e2491 : y ≠ (M.op y y) ∨ (M.op y y) = (k y y) := by
          first
          | (have i₁ := b0e70 y
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e70
          | exact resolve b0e70 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e70
        have b0e2492 : (M.op y y) = (k y y) := by
          first
          | (have j1 := b0e15 y y
             grind)
          | (have r₁ := b0e2491
             have r₂ := b0e15 y y
             grind)
          | exact resolve b0e2491 b0e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e2491
        have b0e8167 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b0e190 (σ y)
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e190
          | exact resolve b0e190 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e190
        have b0e8173 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have j1 := b0e15 (σ y) (σ y)
             grind)
          | (have r₁ := b0e8167
             have r₂ := b0e15 (σ y) (σ y)
             grind)
          | exact resolve b0e8167 b0e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e8167
        have b0e8181 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b0e8173
             have i₂ := b0e16 y y
             grind)
          | exact superpose b0e16 b0e8173
          | exact resolve b0e8173 b0e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e8173
        have b0e8184 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b0e8181
             have i₂ := b0e2492
             grind)
          | exact superpose b0e2492 b0e8181
          | exact resolve b0e8181 b0e2492
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e2492 b0e8181
        have b0e8192 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op y y)) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b0e11 (σ y) X0 (σ y)
             have i₂ := b0e8184
             grind)
          | exact superpose b0e8184 b0e11
          | exact resolve b0e11 b0e8184
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e8184
        have b0e9162 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y y)) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b0e604 y x X0
             have i₂ := b0e42
             grind)
          | exact superpose b0e42 b0e604
          | (have j0 := b0e604 y x x
             grind)
          | exact resolve b0e604 b0e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e42 b0e604
        have b0e9327 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y y)) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have j0 := b0e9162 X0
             grind)
          | (have r₁ := b0e9162 X0
             have r₂ := b0e21
             grind)
          | exact resolve b0e9162 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e9162
        have b0e9360 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b0e9327 X0
             have i₂ := b0e8192 X0
             grind)
          | exact superpose b0e8192 b0e9327
          | exact resolve b0e9327 b0e8192
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e8192 b0e9327
        have b0e9425 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b0e47
             have i₂ := b0e9360 (σ x)
             grind)
          | exact superpose b0e9360 b0e47
          | exact resolve b0e47 b0e9360
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e47
        have b0e9498 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x x)) (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b0e144 (σ x)
             have i₂ := b0e9360 (σ x)
             grind)
          | exact superpose b0e9360 b0e144
          | exact resolve b0e144 b0e9360
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e9532 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b0e9498
             have i₂ := b0e144 (σ y)
             grind)
          | exact superpose b0e144 b0e9498
          | exact resolve b0e9498 b0e144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e144 b0e9498
        have b0e9592 : (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b0e9425
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e9425
          | exact resolve b0e9425 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e9425
        have b0e9612 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b0e9532
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e9532
          | exact resolve b0e9532 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e9532
        have b0e9640 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e9612
             have i₂ := b0e9360 (σ y)
             grind)
          | exact superpose b0e9360 b0e9612
          | exact resolve b0e9612 b0e9360
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e9360 b0e9612
        have b0e9946 : (M.op x x) = (τ (σ y)) := by
          first
          | (have i₁ := b0e12 (M.op x x)
             have i₂ := b0e9592
             grind)
          | exact superpose b0e9592 b0e12
          | exact resolve b0e12 b0e9592
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e9592
        have b0e9979 : y = (M.op x x) := by
          first
          | (have i₁ := b0e9946
             have i₂ := b0e12 y
             grind)
          | exact superpose b0e12 b0e9946
          | exact resolve b0e9946 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e9946
        have b0e11758 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b0e31 x
             have i₂ := b0e9979
             grind)
          | exact superpose b0e9979 b0e31
          | exact resolve b0e31 b0e9979
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e31
        have b0e11759 : (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b0e27 x
             have i₂ := b0e9979
             grind)
          | exact superpose b0e9979 b0e27
          | exact resolve b0e27 b0e9979
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e27 b0e9979
        have b0e11805 : y = (M.op y y) := by
          first
          | (have i₁ := b0e11759
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e11759
          | exact resolve b0e11759 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e11759
        have b0e11806 : x = (M.op y y) := by
          first
          | (have i₁ := b0e11758
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e11758
          | exact resolve b0e11758 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e11758
        have b0e11826 : x = y := by
          first
          | (have i₁ := b0e11806
             have i₂ := b0e11805
             grind)
          | exact superpose b0e11805 b0e11806
          | exact resolve b0e11806 b0e11805
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e11805 b0e11806
        have b0e13395 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e21
             have i₂ := b0e11826
             grind)
          | exact superpose b0e11826 b0e21
          | exact resolve b0e21 b0e11826
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e21 b0e11826
        have b0e13477 : False := by grind
        exact b0e13477
      · have b1e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b1e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e18 : y = (M.op y x) := by grind
        have b1e19 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b1e20 : x ≠ (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b1e26 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 x) y) := by
          intro X0
          first
          | (have i₁ := b1e11 X0 y x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e11
          | exact resolve b1e11 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ x)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e11 X0 (σ y) (σ x)
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e11
          | exact resolve b1e11 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : y ≠ y ∨ (k x y) = (M.op x x) := by
          first
          | (have i₁ := b1e14 x y
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e14
          | (have j0 := b1e14 x y
             grind)
          | (have r₁ := b1e14 x y
             have r₂ := b1e18
             grind)
          | exact resolve b1e14 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e14 (σ x) (σ y)
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e14
          | (have j0 := b1e14 (σ x) (σ y)
             grind)
          | (have r₁ := b1e14 (σ x) (σ y)
             have r₂ := b1e19
             grind)
          | exact resolve b1e14 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b1e35
        have b1e38 : (k x y) = (M.op x x) := by grind
        clear b1e33
        have b1e40 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e37
             have i₂ := b1e16 x y
             grind)
          | exact superpose b1e16 b1e37
          | exact resolve b1e37 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e42 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e40
             have i₂ := b1e38
             grind)
          | exact superpose b1e38 b1e40
          | exact resolve b1e40 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38 b1e40
        have b1e45 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X1 X0
             have i₂ := b1e15 (σ X1) (σ X0)
             grind)
          | exact superpose b1e15 b1e16
          | (have j1 := b1e15 (σ X1) (σ X0)
             grind)
          | exact resolve b1e16 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e47 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 y) ∨ (M.op y y) = (k y (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e14 y (M.op X0 x)
             have i₂ := b1e26 X0
             grind)
          | exact superpose b1e26 b1e14
          | (have j0 := b1e14 y (M.op X0 x)
             grind)
          | exact resolve b1e14 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e124 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (σ x))) = (M.op (M.op X1 (σ y)) (M.op X0 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 X1 (M.op X0 (σ x)) (σ y)
             have i₂ := b1e27 X0
             grind)
          | exact superpose b1e27 b1e11
          | exact resolve b1e11 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e127 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (σ x))) := by
          intro X0 X1
          first
          | (have i₁ := b1e124 X0 X1
             have i₂ := b1e11 X1 X0 (σ y)
             grind)
          | exact superpose b1e11 b1e124
          | exact resolve b1e124 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e124
        have b1e302 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x x))) := by
          intro X0
          first
          | (have i₁ := b1e127 (σ x) X0
             have i₂ := b1e42
             grind)
          | exact superpose b1e42 b1e127
          | exact resolve b1e127 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e127
        have b1e423 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e17
             have i₂ := b1e45 x y
             grind)
          | exact superpose b1e45 b1e17
          | (have j1 := b1e45 x y
             grind)
          | exact resolve b1e17 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1730 : y ≠ (M.op y y) ∨ (M.op y y) = (k y y) := by
          first
          | (have i₁ := b1e47 y
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e47
          | exact resolve b1e47 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e1731 : (M.op y y) = (k y y) := by
          first
          | (have j1 := b1e15 y y
             grind)
          | (have r₁ := b1e1730
             have r₂ := b1e15 y y
             grind)
          | exact resolve b1e1730 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1730
        have b1e2513 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e423
             have i₂ := b1e15 y x
             grind)
          | exact superpose b1e15 b1e423
          | (have j1 := b1e15 (σ y) (σ x)
             grind)
          | exact resolve b1e423 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e423
        have b1e2514 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
        clear b1e2513
        have b1e2515 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b1e2514
             have r₂ := b1e20
             grind)
          | exact resolve b1e2514 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2514
        have b1e2523 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b1e14 (σ y) (σ x)
             have i₂ := b1e2515
             grind)
          | exact superpose b1e2515 b1e14
          | (have j0 := b1e14 (σ y) (σ x)
             grind)
          | (have r₁ := b1e14 (σ y) (σ x)
             have r₂ := b1e2515
             grind)
          | exact resolve b1e14 b1e2515
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2515
        have b1e2535 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b1e2523
        have b1e2540 : (M.op (σ y) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e2535
             have i₂ := b1e16 y x
             grind)
          | exact superpose b1e16 b1e2535
          | exact resolve b1e2535 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2535
        have b1e3133 : (σ (k y x)) = (σ (k y y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b1e45 y y
             have i₂ := b1e2540
             grind)
          | exact superpose b1e2540 b1e45
          | exact resolve b1e45 b1e2540
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e3142 : (σ y) ≠ (σ (k y x)) ∨ (σ (k y x)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e14 (σ y) (σ y)
             have i₂ := b1e2540
             grind)
          | exact superpose b1e2540 b1e14
          | exact resolve b1e14 b1e2540
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2540
        have b1e3158 : (σ (k y x)) = (σ (k y y)) ∨ (σ y) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e3142
             have i₂ := b1e16 y y
             grind)
          | exact superpose b1e16 b1e3142
          | exact resolve b1e3142 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3142
        have b1e3162 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b1e3133
             have i₂ := b1e1731
             grind)
          | exact superpose b1e1731 b1e3133
          | exact resolve b1e3133 b1e1731
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3133
        have b1e3166 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ y) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e3158
             have i₂ := b1e1731
             grind)
          | exact superpose b1e1731 b1e3158
          | exact resolve b1e3158 b1e1731
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1731 b1e3158
        have b1e3169 : (σ (k y x)) = (σ (M.op y y)) := by
          first
          | (have r₁ := b1e3166
             have r₂ := b1e3162
             grind)
          | exact resolve b1e3166 b1e3162
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3162 b1e3166
        have b1e3655 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e3169
             have i₂ := b1e15 y x
             grind)
          | exact superpose b1e15 b1e3169
          | (have j1 := b1e15 y x
             grind)
          | exact resolve b1e3169 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e3659 : (k y x) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b1e12 (k y x)
             have i₂ := b1e3169
             grind)
          | exact superpose b1e3169 b1e12
          | exact resolve b1e12 b1e3169
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3169
        have b1e3687 : (M.op y y) = (k y x) := by
          first
          | (have i₁ := b1e3659
             have i₂ := b1e12 (M.op y y)
             grind)
          | exact superpose b1e12 b1e3659
          | exact resolve b1e3659 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3659
        have b1e3689 : (σ (M.op x y)) = (σ (M.op y y)) := by
          first
          | (have r₁ := b1e3655
             have r₂ := b1e20
             grind)
          | exact resolve b1e3655 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3655
        have b1e4344 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e15 y x
             have i₂ := b1e3687
             grind)
          | exact superpose b1e3687 b1e15
          | (have j0 := b1e15 y x
             grind)
          | exact resolve b1e15 b1e3687
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3687
        have b1e4345 : (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b1e4344
             have r₂ := b1e20
             grind)
          | exact resolve b1e4344 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4344
        have b1e5522 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 y) (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b1e11 X0 x y
             have i₂ := b1e4345
             grind)
          | exact superpose b1e4345 b1e11
          | exact resolve b1e11 b1e4345
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4345
        have b1e5555 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e5522 X0
             have i₂ := b1e11 X0 y y
             grind)
          | exact superpose b1e11 b1e5522
          | exact resolve b1e5522 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5522
        have b1e6529 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) := by
          intro X0
          first
          | (have i₁ := b1e302 X0
             have i₂ := b1e5555 x
             grind)
          | exact superpose b1e5555 b1e302
          | exact resolve b1e302 b1e5555
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e302
        have b1e6533 : y = (M.op y y) := by
          first
          | (have i₁ := b1e18
             have i₂ := b1e5555 y
             grind)
          | exact superpose b1e5555 b1e18
          | exact resolve b1e18 b1e5555
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e6541 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y y))) := by
          intro X0
          first
          | (have i₁ := b1e6529 X0
             have i₂ := b1e3689
             grind)
          | exact superpose b1e3689 b1e6529
          | exact resolve b1e6529 b1e3689
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3689 b1e6529
        have b1e6608 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e6541 X0
             have i₂ := b1e6533
             grind)
          | exact superpose b1e6533 b1e6541
          | exact resolve b1e6541 b1e6533
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6533 b1e6541
        have b1e15068 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e42
             have i₂ := b1e6608 (σ x)
             grind)
          | exact superpose b1e6608 b1e42
          | exact resolve b1e42 b1e6608
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42 b1e6608
        have b1e15096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e15068
             have i₂ := b1e5555 x
             grind)
          | exact superpose b1e5555 b1e15068
          | exact resolve b1e15068 b1e5555
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5555 b1e15068
        have b1e15174 : False := by grind
        exact b1e15174
    · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
      · have b2e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b2e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e18 : y = (M.op y x) := by grind
        have b2e20 : x = (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e17
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e17
          | exact resolve b2e17 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 (τ X0) X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e16
          | exact resolve b2e16 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e26 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X1 X2))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e11 (M.op X0 X2) X3 (M.op X1 X2)
             have i₂ := b2e11 X0 X1 X2
             grind)
          | exact superpose b2e11 b2e11
          | exact resolve b2e11 b2e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e27 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 x) y) := by
          intro X0
          first
          | (have i₁ := b2e11 X0 y x
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e11
          | exact resolve b2e11 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 y) x) := by
          intro X0
          first
          | (have i₁ := b2e11 X0 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e11
          | exact resolve b2e11 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : x ≠ x ∨ (M.op y y) = (k y x) := by
          first
          | (have i₁ := b2e14 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e14
          | (have j0 := b2e14 y x
             grind)
          | (have r₁ := b2e14 y x
             have r₂ := b2e20
             grind)
          | exact resolve b2e14 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e37 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (k (M.op X1 X2) (M.op X0 X2)) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e14 (M.op X1 X2) (M.op X0 X2)
             have i₂ := b2e11 X0 X1 X2
             grind)
          | exact superpose b2e11 b2e14
          | (have j0 := b2e14 (M.op X1 X2) (M.op X0 X2)
             grind)
          | (have r₁ := b2e14 (M.op X1 X1) (M.op X0 X1)
             have r₂ := b2e11 X0 X1 X1
             grind)
          | exact resolve b2e14 b2e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : (M.op y y) = (k y x) := by grind
        clear b2e36
        have b2e40 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (k (M.op X1 X2) (M.op X0 X2)) = (M.op X1 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e37 X0 X1 X2
             have i₂ := b2e11 X1 X1 X2
             grind)
          | exact superpose b2e11 b2e37
          | (have j0 := b2e37 X0 X1 X2
             grind)
          | exact resolve b2e37 b2e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X1 X0
             have i₂ := b2e15 (σ X1) (σ X0)
             grind)
          | exact superpose b2e15 b2e16
          | (have j1 := b2e15 (σ X1) (σ X0)
             grind)
          | exact resolve b2e16 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e65 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op (M.op X1 x) (M.op X0 x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e11 X1 (M.op X0 y) x
             have i₂ := b2e28 X0
             grind)
          | exact superpose b2e28 b2e11
          | exact resolve b2e11 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e66 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op X0 x) (M.op X1 x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e11 (M.op X0 y) X1 x
             have i₂ := b2e28 X0
             grind)
          | exact superpose b2e28 b2e11
          | exact resolve b2e11 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e67 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e66 X0 X1
             have i₂ := b2e11 X0 X1 x
             grind)
          | exact superpose b2e11 b2e66
          | exact resolve b2e66 b2e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e68 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 y)) := by
          intro X0 X1
          first
          | (have i₁ := b2e65 X0 X1
             have i₂ := b2e11 X1 X0 x
             grind)
          | exact superpose b2e11 b2e65
          | exact resolve b2e65 b2e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e89 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (k (τ X0) X1)
             have i₂ := b2e22 X0 X1
             grind)
          | exact superpose b2e22 b2e12
          | exact resolve b2e12 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22
        have b2e168 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op X2 (M.op y X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e67 X0 (M.op X2 (M.op y X1))
             have i₂ := b2e26 X0 y X1 X2
             grind)
          | exact superpose b2e26 b2e67
          | exact resolve b2e67 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e310 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e89 X1 (τ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e89
          | exact resolve b2e89 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e89
        have b2e345 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e40 X1 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e398 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ (k X0 X1)) (M.op X2 (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e11 (σ X1) X2 (σ X0)
             have i₂ := b2e44 X1 X0
             grind)
          | exact superpose b2e44 b2e11
          | (have j1 := b2e44 X1 X0
             grind)
          | exact resolve b2e11 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e407 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e44 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1538 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e407 (τ X1) (τ X0)
             have i₂ := b2e310 X1 X0
             grind)
          | exact superpose b2e310 b2e407
          | (have j0 := b2e407 (τ X1) (τ X0)
             grind)
          | exact resolve b2e407 b2e310
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e310
        have b2e1542 : (σ x) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e407 x y
             have i₂ := b2e38
             grind)
          | exact superpose b2e38 b2e407
          | (have j0 := b2e407 x y
             grind)
          | exact resolve b2e407 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e407
        have b2e1547 : (σ x) ≠ (σ (M.op y y)) := by
          first
          | (have r₁ := b2e1542
             have r₂ := b2e21
             grind)
          | exact resolve b2e1542 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1542
        have b2e1549 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e1538 X0 X1
             have i₂ := b2e13 (k X0 X1)
             grind)
          | exact superpose b2e13 b2e1538
          | (have j0 := b2e1538 X0 X1
             grind)
          | exact resolve b2e1538 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1538
        have b2e1551 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e1549 X0 X1
             have i₂ := b2e13 X1
             grind)
          | exact superpose b2e13 b2e1549
          | (have j0 := b2e1549 X0 X1
             grind)
          | exact resolve b2e1549 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1549
        have b2e1552 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e1551 X0 X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e1551
          | (have j0 := b2e1551 X0 X1
             grind)
          | exact resolve b2e1551 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1551
        have b2e1553 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e1552 X0 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e1552
          | (have j0 := b2e1552 X0 X1
             grind)
          | exact resolve b2e1552 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1552
        have b2e4477 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y y)) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e398 y x X0
             have i₂ := b2e38
             grind)
          | exact superpose b2e38 b2e398
          | (have j0 := b2e398 y x x
             grind)
          | exact resolve b2e398 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e398
        have b2e4578 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y y)) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have j0 := b2e4477 X0
             grind)
          | (have r₁ := b2e4477 X0
             have r₂ := b2e21
             grind)
          | exact resolve b2e4477 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21 b2e4477
        have b2e4624 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ (M.op y y))) = (M.op X0 (M.op (σ x) y)) := by
          intro X0
          first
          | (have i₁ := b2e168 X0 (σ y) (σ (M.op y y))
             have i₂ := b2e4578 y
             grind)
          | exact superpose b2e4578 b2e168
          | exact resolve b2e168 b2e4578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e168
        have b2e4625 : ∀ X0 X1 : G, (M.op (σ (M.op y y)) X1) = (M.op (M.op (σ x) X0) (M.op X1 (M.op X0 (σ y)))) := by
          intro X0 X1
          first
          | (have i₁ := b2e11 (σ (M.op y y)) X1 (M.op X0 (σ y))
             have i₂ := b2e4578 X0
             grind)
          | exact superpose b2e4578 b2e11
          | exact resolve b2e11 b2e4578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4578
        have b2e4670 : ∀ X1 : G, (M.op (σ (M.op y y)) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
          intro X1
          first
          | (have i₁ := b2e4625 x X1
             have i₂ := b2e26 (σ x) x (σ y) X1
             grind)
          | exact superpose b2e26 b2e4625
          | exact resolve b2e4625 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e4625
        have b2e4671 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ y)) (σ (M.op y y))) := by
          intro X0
          first
          | (have i₁ := b2e4624 X0
             have i₂ := b2e68 (σ x) X0
             grind)
          | exact superpose b2e68 b2e4624
          | exact resolve b2e4624 b2e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68 b2e4624
        have b2e8507 : (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e4670 (σ (M.op y y))
             have i₂ := b2e4671 (σ x)
             grind)
          | exact superpose b2e4671 b2e4670
          | exact resolve b2e4670 b2e4671
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4670 b2e4671
        have b2e15903 : (M.op (σ x) (σ x)) = (σ (k (M.op y y) (M.op y y))) ∨ (σ (M.op y y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e44 (M.op y y) (M.op y y)
             have i₂ := b2e8507
             grind)
          | exact superpose b2e8507 b2e44
          | exact resolve b2e44 b2e8507
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8507
        have b2e15980 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op y y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e15903
             have i₂ := b2e345 y y
             grind)
          | exact superpose b2e345 b2e15903
          | exact resolve b2e15903 b2e345
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15903
        have b2e15981 : (σ (M.op y y)) = (M.op (σ x) (σ x)) := by grind
        clear b2e15980
        have b2e16108 : (σ (M.op y y)) = (σ (k x x)) ∨ (σ x) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e44 x x
             have i₂ := b2e15981
             grind)
          | exact superpose b2e15981 b2e44
          | exact resolve b2e44 b2e15981
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44 b2e15981
        have b2e16184 : (σ (M.op y y)) = (σ (k x x)) := by
          first
          | (have r₁ := b2e16108
             have r₂ := b2e1547
             grind)
          | exact resolve b2e16108 b2e1547
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16108
        have b2e16320 : (k x x) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b2e12 (k x x)
             have i₂ := b2e16184
             grind)
          | exact superpose b2e16184 b2e12
          | exact resolve b2e12 b2e16184
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e16370 : (M.op y y) = (k x x) := by
          first
          | (have i₁ := b2e16320
             have i₂ := b2e12 (M.op y y)
             grind)
          | exact superpose b2e12 b2e16320
          | exact resolve b2e16320 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16320
        have b2e16926 : (M.op y y) = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e15 x x
             have i₂ := b2e16370
             grind)
          | exact superpose b2e16370 b2e15
          | (have j0 := b2e15 x x
             grind)
          | exact resolve b2e15 b2e16370
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e16935 : x ≠ (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e1553 x x
             have i₂ := b2e16370
             grind)
          | exact superpose b2e16370 b2e1553
          | (have j0 := b2e1553 x x
             grind)
          | exact resolve b2e1553 b2e16370
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1553 b2e16370
        have b2e19252 : (M.op x y) = (M.op (M.op y y) y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e27 x
             have i₂ := b2e16926
             grind)
          | exact superpose b2e16926 b2e27
          | exact resolve b2e27 b2e16926
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e16926
        have b2e19332 : (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e19252
             have i₂ := b2e67 y y
             grind)
          | exact superpose b2e67 b2e19252
          | exact resolve b2e19252 b2e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67 b2e19252
        have b2e19369 : x = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e19332
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19332
          | exact resolve b2e19332 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19332
        have b2e19393 : x = (M.op x x) := by
          first
          | (have r₁ := b2e19369
             have r₂ := b2e16935
             grind)
          | exact resolve b2e19369 b2e16935
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16935 b2e19369
        have b2e19635 : x = (k x x) := by
          first
          | (have i₁ := b2e345 x x
             have i₂ := b2e19393
             grind)
          | exact superpose b2e19393 b2e345
          | exact resolve b2e345 b2e19393
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e345 b2e19393
        have b2e19973 : (σ x) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e16184
             have i₂ := b2e19635
             grind)
          | exact superpose b2e19635 b2e16184
          | exact resolve b2e16184 b2e19635
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16184 b2e19635
        have b2e19996 : False := by grind
        exact b2e19996
      · have b3e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b3e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e18 : y = (M.op y x) := by grind
        have b3e19 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b3e20 : x ≠ (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b3e25 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 x) y) := by
          intro X0
          first
          | (have i₁ := b3e11 X0 y x
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e11
          | exact resolve b3e11 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : y ≠ y ∨ (k x y) = (M.op x x) := by
          first
          | (have i₁ := b3e14 x y
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e14
          | (have j0 := b3e14 x y
             grind)
          | (have r₁ := b3e14 x y
             have r₂ := b3e18
             grind)
          | exact resolve b3e14 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : (k x y) = (M.op x x) := by grind
        clear b3e31
        have b3e39 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X1 X0
             have i₂ := b3e15 (σ X1) (σ X0)
             grind)
          | exact superpose b3e15 b3e16
          | (have j1 := b3e15 (σ X1) (σ X0)
             grind)
          | exact resolve b3e16 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e41 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 y) ∨ (M.op y y) = (k y (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e14 y (M.op X0 x)
             have i₂ := b3e25 X0
             grind)
          | exact superpose b3e25 b3e14
          | (have j0 := b3e14 y (M.op X0 x)
             grind)
          | exact resolve b3e14 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e248 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e17
             have i₂ := b3e39 x y
             grind)
          | exact superpose b3e39 b3e17
          | (have j1 := b3e39 x y
             grind)
          | exact resolve b3e17 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e258 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e39 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e894 : (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e258 y x
             have i₂ := b3e34
             grind)
          | exact superpose b3e34 b3e258
          | (have j0 := b3e258 y x
             grind)
          | exact resolve b3e258 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e258
        have b3e899 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have r₁ := b3e894
             have r₂ := b3e19
             grind)
          | exact resolve b3e894 b3e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e894
        have b3e908 : y ≠ (M.op y y) ∨ (M.op y y) = (k y y) := by
          first
          | (have i₁ := b3e41 y
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e41
          | exact resolve b3e41 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e909 : (M.op y y) = (k y y) := by
          first
          | (have j1 := b3e15 y y
             grind)
          | (have r₁ := b3e908
             have r₂ := b3e15 y y
             grind)
          | exact resolve b3e908 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e908
        have b3e1020 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e248
             have i₂ := b3e15 y x
             grind)
          | exact superpose b3e15 b3e248
          | (have j1 := b3e15 (σ y) (σ x)
             grind)
          | exact resolve b3e248 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e248
        have b3e1021 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
        clear b3e1020
        have b3e1022 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b3e1021
             have r₂ := b3e20
             grind)
          | exact resolve b3e1021 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1021
        have b3e1027 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e14 (σ y) (σ x)
             have i₂ := b3e1022
             grind)
          | exact superpose b3e1022 b3e14
          | (have j0 := b3e14 (σ y) (σ x)
             grind)
          | (have r₁ := b3e14 (σ y) (σ x)
             have r₂ := b3e1022
             grind)
          | exact resolve b3e14 b3e1022
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1022
        have b3e1039 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b3e1027
        have b3e1043 : (σ (k y x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e1039
             have i₂ := b3e16 y x
             grind)
          | exact superpose b3e16 b3e1039
          | exact resolve b3e1039 b3e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1039
        have b3e2211 : (σ (k y x)) = (σ (k y y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b3e39 y y
             have i₂ := b3e1043
             grind)
          | exact superpose b3e1043 b3e39
          | exact resolve b3e39 b3e1043
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e2219 : (σ y) ≠ (σ (k y x)) ∨ (σ (k y x)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e14 (σ y) (σ y)
             have i₂ := b3e1043
             grind)
          | exact superpose b3e1043 b3e14
          | exact resolve b3e14 b3e1043
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1043
        have b3e2247 : (σ (k y x)) = (σ (k y y)) ∨ (σ y) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b3e2219
             have i₂ := b3e16 y y
             grind)
          | exact superpose b3e16 b3e2219
          | exact resolve b3e2219 b3e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2219
        have b3e2250 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b3e2211
             have i₂ := b3e909
             grind)
          | exact superpose b3e909 b3e2211
          | exact resolve b3e2211 b3e909
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2211
        have b3e2259 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ y) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b3e2247
             have i₂ := b3e909
             grind)
          | exact superpose b3e909 b3e2247
          | exact resolve b3e2247 b3e909
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e909 b3e2247
        have b3e2264 : (σ (k y x)) = (σ (M.op y y)) := by
          first
          | (have r₁ := b3e2259
             have r₂ := b3e2250
             grind)
          | exact resolve b3e2259 b3e2250
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2250 b3e2259
        have b3e2624 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e2264
             have i₂ := b3e15 y x
             grind)
          | exact superpose b3e15 b3e2264
          | (have j1 := b3e15 y x
             grind)
          | exact resolve b3e2264 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2628 : (k y x) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b3e12 (k y x)
             have i₂ := b3e2264
             grind)
          | exact superpose b3e2264 b3e12
          | exact resolve b3e12 b3e2264
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2264
        have b3e2657 : (M.op y y) = (k y x) := by
          first
          | (have i₁ := b3e2628
             have i₂ := b3e12 (M.op y y)
             grind)
          | exact superpose b3e12 b3e2628
          | exact resolve b3e2628 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2628
        have b3e2659 : (σ (M.op x y)) = (σ (M.op y y)) := by
          first
          | (have r₁ := b3e2624
             have r₂ := b3e20
             grind)
          | exact resolve b3e2624 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2624
        have b3e3198 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e15 y x
             have i₂ := b3e2657
             grind)
          | exact superpose b3e2657 b3e15
          | (have j0 := b3e15 y x
             grind)
          | exact resolve b3e15 b3e2657
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2657
        have b3e3199 : (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b3e3198
             have r₂ := b3e20
             grind)
          | exact resolve b3e3198 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3198
        have b3e3506 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 y) (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b3e11 X0 x y
             have i₂ := b3e3199
             grind)
          | exact superpose b3e3199 b3e11
          | exact resolve b3e11 b3e3199
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3199
        have b3e3542 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e3506 X0
             have i₂ := b3e11 X0 y y
             grind)
          | exact superpose b3e11 b3e3506
          | exact resolve b3e3506 b3e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3506
        have b3e4768 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e899
             have i₂ := b3e3542 x
             grind)
          | exact superpose b3e3542 b3e899
          | exact resolve b3e899 b3e3542
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e899
        have b3e4772 : y = (M.op y y) := by
          first
          | (have i₁ := b3e18
             have i₂ := b3e3542 y
             grind)
          | exact superpose b3e3542 b3e18
          | exact resolve b3e18 b3e3542
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3542
        have b3e4780 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e4768
             have i₂ := b3e2659
             grind)
          | exact superpose b3e2659 b3e4768
          | exact resolve b3e4768 b3e2659
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2659 b3e4768
        have b3e4829 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e4780
             have i₂ := b3e4772
             grind)
          | exact superpose b3e4772 b3e4780
          | exact resolve b3e4780 b3e4772
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4772 b3e4780
        have b3e4830 : False := by grind
        exact b3e4830
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
      · have b4e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b4e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b4e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b4e15 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b4e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b4e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b4e18 : y ≠ (M.op y x) := by grind
        have b4e19 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b4e20 : x = (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b4e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b4e17
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e17
          | exact resolve b4e17 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e25 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b4e11 (σ y) X0 (σ x)
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e11
          | exact resolve b4e11 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e28 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ x)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b4e11 X0 (σ y) (σ x)
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e11
          | exact resolve b4e11 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e34 : x ≠ x ∨ (k y x) = (M.op y y) := by
          first
          | (have i₁ := b4e14 y x
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e14
          | (have j0 := b4e14 y x
             grind)
          | (have r₁ := b4e14 y x
             have r₂ := b4e20
             grind)
          | exact resolve b4e14 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e36 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b4e14 (σ x) (σ y)
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e14
          | (have j0 := b4e14 (σ x) (σ y)
             grind)
          | (have r₁ := b4e14 (σ x) (σ y)
             have r₂ := b4e19
             grind)
          | exact resolve b4e14 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e37 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (k (M.op X1 X2) (M.op X0 X2)) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b4e14 (M.op X1 X2) (M.op X0 X2)
             have i₂ := b4e11 X0 X1 X2
             grind)
          | exact superpose b4e11 b4e14
          | (have j0 := b4e14 (M.op X1 X2) (M.op X0 X2)
             grind)
          | (have r₁ := b4e14 (M.op X1 X1) (M.op X0 X1)
             have r₂ := b4e11 X0 X1 X1
             grind)
          | exact resolve b4e14 b4e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e38 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b4e36
        have b4e39 : (k y x) = (M.op y y) := by grind
        clear b4e34
        have b4e40 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (k (M.op X1 X2) (M.op X0 X2)) = (M.op X1 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b4e37 X0 X1 X2
             have i₂ := b4e11 X1 X1 X2
             grind)
          | exact superpose b4e11 b4e37
          | (have j0 := b4e37 X0 X1 X2
             grind)
          | exact resolve b4e37 b4e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e37
        have b4e41 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b4e38
             have i₂ := b4e16 x y
             grind)
          | exact superpose b4e16 b4e38
          | exact resolve b4e38 b4e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e38
        have b4e45 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b4e16 X1 X0
             have i₂ := b4e15 (σ X1) (σ X0)
             grind)
          | exact superpose b4e15 b4e16
          | (have j1 := b4e15 (σ X1) (σ X0)
             grind)
          | exact resolve b4e16 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e85 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b4e14 (σ x) (σ x)
             have i₂ := b4e41
             grind)
          | exact superpose b4e41 b4e14
          | exact resolve b4e14 b4e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e86 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (σ (k x y))) := by
          intro X0
          first
          | (have i₁ := b4e11 X0 (σ x) (σ x)
             have i₂ := b4e41
             grind)
          | exact superpose b4e41 b4e11
          | exact resolve b4e11 b4e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e88 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b4e85
             have i₂ := b4e16 x x
             grind)
          | exact superpose b4e16 b4e85
          | exact resolve b4e85 b4e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e85
        have b4e99 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ (k x y))) := by
          first
          | (have i₁ := b4e25 (σ x)
             have i₂ := b4e41
             grind)
          | exact superpose b4e41 b4e25
          | exact resolve b4e25 b4e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e100 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (k (M.op X0 (σ x)) (σ y)) = (M.op (M.op X0 (σ x)) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b4e14 (M.op X0 (σ x)) (σ y)
             have i₂ := b4e25 X0
             grind)
          | exact superpose b4e25 b4e14
          | (have j0 := b4e14 X0 (σ y)
             grind)
          | exact resolve b4e14 b4e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e25
        have b4e105 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (k (M.op X0 (σ x)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b4e100 X0
             have i₂ := b4e11 X0 X0 (σ x)
             grind)
          | exact superpose b4e11 b4e100
          | (have j0 := b4e100 X0
             grind)
          | exact resolve b4e100 b4e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e100
        have b4e106 : (σ y) = (M.op (σ y) (σ (k x y))) := by
          first
          | (have i₁ := b4e99
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e99
          | exact resolve b4e99 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e99
        have b4e125 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (M.op X0 (σ y)) (M.op X1 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b4e11 (M.op X0 (σ x)) X1 (σ y)
             have i₂ := b4e28 X0
             grind)
          | exact superpose b4e28 b4e11
          | exact resolve b4e11 b4e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e28
        have b4e126 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 (σ x)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b4e125 X0 X1
             have i₂ := b4e11 X0 X1 (σ y)
             grind)
          | exact superpose b4e11 b4e125
          | exact resolve b4e125 b4e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e125
        have b4e129 : (σ y) = (M.op (σ y) (σ (M.op y x))) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b4e106
             have i₂ := b4e15 x y
             grind)
          | exact superpose b4e15 b4e106
          | (have j1 := b4e15 (σ (M.op y x)) (σ y)
             grind)
          | exact resolve b4e106 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e106
        have b4e135 : (σ y) = (M.op (σ y) (σ (M.op y x))) := by
          first
          | (have r₁ := b4e129
             have r₂ := b4e18
             grind)
          | exact resolve b4e129 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e129
        have b4e198 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (k x y)) X0) := by
          intro X0
          first
          | (have i₁ := b4e126 (σ x) X0
             have i₂ := b4e41
             grind)
          | exact superpose b4e41 b4e126
          | exact resolve b4e126 b4e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e351 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op y y) = (k (M.op y X0) (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b4e40 x y X0
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e40
          | (have j0 := b4e40 x y X0
             grind)
          | exact resolve b4e40 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e363 : ∀ X0 : G, (σ (k x y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (M.op X0 (σ x)) (σ (k x y))) := by
          intro X0
          first
          | (have i₁ := b4e40 (σ x) x (σ x)
             have i₂ := b4e41
             grind)
          | exact superpose b4e41 b4e40
          | exact resolve b4e40 b4e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e368 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b4e40 X1 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e40
        have b4e422 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b4e45 x x
             have i₂ := b4e41
             grind)
          | exact superpose b4e41 b4e45
          | exact resolve b4e45 b4e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e440 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b4e45 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e45
        have b4e444 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have r₁ := b4e422
             have r₂ := b4e88
             grind)
          | exact resolve b4e422 b4e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e88 b4e422
        have b4e450 : (k x x) = (τ (σ (k x y))) := by
          first
          | (have i₁ := b4e12 (k x x)
             have i₂ := b4e444
             grind)
          | exact superpose b4e444 b4e12
          | exact resolve b4e12 b4e444
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e463 : (k x y) = (k x x) := by
          first
          | (have i₁ := b4e450
             have i₂ := b4e12 (k x y)
             grind)
          | exact superpose b4e12 b4e450
          | exact resolve b4e450 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e450
        have b4e484 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ y)) := by
          first
          | (have i₁ := b4e368 (σ x) (σ y)
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e368
          | exact resolve b4e368 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e497 : (σ (k x y)) = (k (σ (k x y)) (σ y)) := by
          first
          | (have i₁ := b4e484
             have i₂ := b4e41
             grind)
          | exact superpose b4e41 b4e484
          | exact resolve b4e484 b4e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e484
        have b4e508 : (σ (k x y)) = (σ (k (k x y) y)) := by
          first
          | (have i₁ := b4e497
             have i₂ := b4e16 (k x y) y
             grind)
          | exact superpose b4e16 b4e497
          | exact resolve b4e497 b4e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e497
        have b4e514 : (M.op x x) = (k x y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b4e15 x x
             have i₂ := b4e463
             grind)
          | exact superpose b4e463 b4e15
          | (have j0 := b4e15 x x
             grind)
          | exact resolve b4e15 b4e463
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e463
        have b4e606 : (σ y) ≠ (σ y) ∨ (k (σ (M.op y x)) (σ y)) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by
          first
          | (have i₁ := b4e14 (σ (M.op y x)) (σ y)
             have i₂ := b4e135
             grind)
          | exact superpose b4e135 b4e14
          | (have j0 := b4e14 (σ (M.op y x)) (σ y)
             grind)
          | (have r₁ := b4e14 (σ (M.op y x)) (σ y)
             have r₂ := b4e135
             grind)
          | exact resolve b4e14 b4e135
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e614 : (k (σ (M.op y x)) (σ y)) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by grind
        clear b4e606
        have b4e618 : (σ (k (M.op y x) y)) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by
          first
          | (have i₁ := b4e614
             have i₂ := b4e16 (M.op y x) y
             grind)
          | exact superpose b4e16 b4e614
          | exact resolve b4e614 b4e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e614
        have b4e633 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y x)) X0) ∨ y = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b4e198 X0
             have i₂ := b4e15 x y
             grind)
          | exact superpose b4e15 b4e198
          | (have j1 := b4e15 x y
             grind)
          | exact resolve b4e198 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e198
        have b4e691 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y x)) X0) := by
          intro X0
          first
          | (have j0 := b4e633 X0
             grind)
          | (have r₁ := b4e633 X0
             have r₂ := b4e18
             grind)
          | exact resolve b4e633 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e633
        have b4e702 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (σ (M.op y x))) ∨ y = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b4e86 X0
             have i₂ := b4e15 x y
             grind)
          | exact superpose b4e15 b4e86
          | (have j1 := b4e15 (σ (M.op y x)) (M.op X0 (σ x))
             grind)
          | exact resolve b4e86 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e86
        have b4e724 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (σ (M.op y x))) := by
          intro X0
          first
          | (have j0 := b4e702 X0
             grind)
          | (have r₁ := b4e702 X0
             have r₂ := b4e18
             grind)
          | exact resolve b4e702 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e702
        have b4e733 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) := by
          intro X0
          first
          | (have i₁ := b4e724 X0
             have i₂ := b4e126 X0 (σ (M.op y x))
             grind)
          | exact superpose b4e126 b4e724
          | exact resolve b4e724 b4e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e126 b4e724
        have b4e848 : (σ (M.op y x)) = (σ (k (M.op y x) y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b4e508
             have i₂ := b4e15 x y
             grind)
          | exact superpose b4e15 b4e508
          | (have j1 := b4e15 x y
             grind)
          | exact resolve b4e508 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e850 : (k (k x y) y) = (τ (σ (k x y))) := by
          first
          | (have i₁ := b4e12 (k (k x y) y)
             have i₂ := b4e508
             grind)
          | exact superpose b4e508 b4e12
          | exact resolve b4e12 b4e508
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e508
        have b4e863 : (k x y) = (k (k x y) y) := by
          first
          | (have i₁ := b4e850
             have i₂ := b4e12 (k x y)
             grind)
          | exact superpose b4e12 b4e850
          | exact resolve b4e850 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e850
        have b4e864 : (σ (M.op y x)) = (σ (k (M.op y x) y)) := by
          first
          | (have r₁ := b4e848
             have r₂ := b4e18
             grind)
          | exact resolve b4e848 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e848
        have b4e1407 : (σ x) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b4e440 x y
             have i₂ := b4e39
             grind)
          | exact superpose b4e39 b4e440
          | (have j0 := b4e440 x y
             grind)
          | exact resolve b4e440 b4e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e39 b4e440
        have b4e1415 : (σ x) ≠ (σ (M.op y y)) := by
          first
          | (have r₁ := b4e1407
             have r₂ := b4e21
             grind)
          | exact resolve b4e1407 b4e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e21 b4e1407
        have b4e2157 : (M.op y x) = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b4e15 x y
             have i₂ := b4e514
             grind)
          | exact superpose b4e514 b4e15
          | (have j0 := b4e15 x y
             grind)
          | exact resolve b4e15 b4e514
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e514
        have b4e2159 : (M.op y x) = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b4e2157
             have r₂ := b4e18
             grind)
          | exact resolve b4e2157 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2157
        have b4e2195 : (σ y) ≠ (σ y) ∨ (M.op (σ (M.op y x)) (σ (M.op y x))) = (k (M.op (σ (M.op y x)) (σ x)) (σ y)) := by
          first
          | (have i₁ := b4e105 (σ (M.op y x))
             have i₂ := b4e135
             grind)
          | exact superpose b4e135 b4e105
          | (have j0 := b4e105 (σ (M.op y x))
             grind)
          | (have r₁ := b4e105 (σ (M.op y x))
             have r₂ := b4e135
             grind)
          | exact resolve b4e105 b4e135
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e105 b4e135
        have b4e2209 : (M.op (σ (M.op y x)) (σ (M.op y x))) = (k (M.op (σ (M.op y x)) (σ x)) (σ y)) := by grind
        clear b4e2195
        have b4e2221 : (k (M.op (σ x) (σ x)) (σ y)) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by
          first
          | (have i₁ := b4e2209
             have i₂ := b4e691 (σ x)
             grind)
          | exact superpose b4e691 b4e2209
          | exact resolve b4e2209 b4e691
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e691 b4e2209
        have b4e2234 : (k (M.op (σ x) (σ x)) (σ y)) = (σ (k (M.op y x) y)) := by
          first
          | (have i₁ := b4e2221
             have i₂ := b4e618
             grind)
          | exact superpose b4e618 b4e2221
          | exact resolve b4e2221 b4e618
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e618 b4e2221
        have b4e2240 : (σ (M.op y x)) = (k (M.op (σ x) (σ x)) (σ y)) := by
          first
          | (have i₁ := b4e2234
             have i₂ := b4e864
             grind)
          | exact superpose b4e864 b4e2234
          | exact resolve b4e2234 b4e864
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e864 b4e2234
        have b4e2243 : (σ (M.op y x)) = (k (σ (k x y)) (σ y)) := by
          first
          | (have i₁ := b4e2240
             have i₂ := b4e41
             grind)
          | exact superpose b4e41 b4e2240
          | exact resolve b4e2240 b4e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2240
        have b4e2245 : (σ (M.op y x)) = (σ (k (k x y) y)) := by
          first
          | (have i₁ := b4e2243
             have i₂ := b4e16 (k x y) y
             grind)
          | exact superpose b4e16 b4e2243
          | exact resolve b4e2243 b4e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2243
        have b4e2247 : (σ (k x y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b4e2245
             have i₂ := b4e863
             grind)
          | exact superpose b4e863 b4e2245
          | exact resolve b4e2245 b4e863
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e863 b4e2245
        have b4e2261 : (k x y) = (τ (σ (M.op y x))) := by
          first
          | (have i₁ := b4e12 (k x y)
             have i₂ := b4e2247
             grind)
          | exact superpose b4e2247 b4e12
          | exact resolve b4e12 b4e2247
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e2262 : ∀ X0 : G, (σ (k (k x y) X0)) = (k (σ (M.op y x)) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b4e16 (k x y) X0
             have i₂ := b4e2247
             grind)
          | exact superpose b4e2247 b4e16
          | exact resolve b4e16 b4e2247
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e2290 : ∀ X0 : G, (σ (k (k x y) X0)) = (σ (k (M.op y x) X0)) := by
          intro X0
          first
          | (have i₁ := b4e2262 X0
             have i₂ := b4e16 (M.op y x) X0
             grind)
          | exact superpose b4e16 b4e2262
          | exact resolve b4e2262 b4e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2262
        have b4e2291 : (M.op y x) = (k x y) := by
          first
          | (have i₁ := b4e2261
             have i₂ := b4e12 (M.op y x)
             grind)
          | exact superpose b4e12 b4e2261
          | exact resolve b4e2261 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2261
        have b4e4229 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) (M.op y x)) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b4e11 X0 x x
             have i₂ := b4e2159
             grind)
          | exact superpose b4e2159 b4e11
          | exact resolve b4e11 b4e2159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2159
        have b4e4257 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b4e4229 X0
             have i₂ := b4e11 X0 y x
             grind)
          | exact superpose b4e11 b4e4229
          | exact resolve b4e4229 b4e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e4229
        have b4e5623 : x ≠ (M.op x y) ∨ x = (M.op x x) := by grind
        clear b4e4257
        have b4e5628 : x = (M.op x x) := by
          first
          | (have r₁ := b4e5623
             have r₂ := b4e20
             grind)
          | exact resolve b4e5623 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e5623
        have b4e5744 : x ≠ x ∨ (M.op y y) = (k (M.op y x) x) := by
          first
          | (have i₁ := b4e351 x
             have i₂ := b4e5628
             grind)
          | exact superpose b4e5628 b4e351
          | (have r₁ := b4e351 x
             have r₂ := b4e5628
             grind)
          | exact resolve b4e351 b4e5628
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e351
        have b4e5768 : x = (k x x) := by
          first
          | (have i₁ := b4e368 x x
             have i₂ := b4e5628
             grind)
          | exact superpose b4e5628 b4e368
          | exact resolve b4e368 b4e5628
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e368 b4e5628
        have b4e5771 : (M.op y y) = (k (M.op y x) x) := by grind
        clear b4e5744
        have b4e5856 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b4e444
             have i₂ := b4e5768
             grind)
          | exact superpose b4e5768 b4e444
          | exact resolve b4e444 b4e5768
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e444 b4e5768
        have b4e5868 : (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b4e5856
             have i₂ := b4e2291
             grind)
          | exact superpose b4e2291 b4e5856
          | exact resolve b4e5856 b4e2291
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e5856
        have b4e6389 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ (M.op y x)) (σ (M.op y x))) = (k (M.op (σ (M.op y x)) (σ x)) (σ (k x y))) := by
          first
          | (have i₁ := b4e363 (σ (M.op y x))
             have i₂ := b4e733 (σ x)
             grind)
          | exact superpose b4e733 b4e363
          | (have j0 := b4e363 (σ x)
             grind)
          | exact resolve b4e363 b4e733
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e363 b4e733
        have b4e6391 : (M.op (σ (M.op y x)) (σ (M.op y x))) = (k (M.op (σ (M.op y x)) (σ x)) (σ (k x y))) := by
          first
          | (have r₁ := b4e6389
             have r₂ := b4e41
             grind)
          | exact resolve b4e6389 b4e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e6389
        have b4e6403 : (M.op (σ (M.op y x)) (σ (M.op y x))) = (k (M.op (σ (M.op y x)) (σ x)) (σ (M.op y x))) := by
          first
          | (have i₁ := b4e6391
             have i₂ := b4e2247
             grind)
          | exact superpose b4e2247 b4e6391
          | exact resolve b4e6391 b4e2247
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2247 b4e6391
        have b4e6414 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ x)) := by
          first
          | (have i₁ := b4e6403
             have i₂ := b4e5868
             grind)
          | exact superpose b4e5868 b4e6403
          | exact resolve b4e6403 b4e5868
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e6403
        have b4e6422 : (σ (k x y)) = (k (σ (k x y)) (σ x)) := by
          first
          | (have i₁ := b4e6414
             have i₂ := b4e41
             grind)
          | exact superpose b4e41 b4e6414
          | exact resolve b4e6414 b4e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e41 b4e6414
        have b4e6429 : (σ (k x y)) = (σ (k (k x y) x)) := by
          first
          | (have i₁ := b4e6422
             have i₂ := b4e16 (k x y) x
             grind)
          | exact superpose b4e16 b4e6422
          | exact resolve b4e6422 b4e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e6422
        have b4e6436 : (σ (k x y)) = (σ (k (M.op y x) x)) := by
          first
          | (have i₁ := b4e6429
             have i₂ := b4e2290 x
             grind)
          | exact superpose b4e2290 b4e6429
          | exact resolve b4e6429 b4e2290
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2290 b4e6429
        have b4e6443 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b4e6436
             have i₂ := b4e5771
             grind)
          | exact superpose b4e5771 b4e6436
          | exact resolve b4e6436 b4e5771
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e5771 b4e6436
        have b4e6446 : (σ (M.op y x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b4e6443
             have i₂ := b4e2291
             grind)
          | exact superpose b4e2291 b4e6443
          | exact resolve b4e6443 b4e2291
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2291 b4e6443
        have b4e6448 : (σ x) = (σ (M.op y y)) := by
          first
          | (have i₁ := b4e6446
             have i₂ := b4e5868
             grind)
          | exact superpose b4e5868 b4e6446
          | exact resolve b4e6446 b4e5868
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e5868 b4e6446
        have b4e6450 : False := by grind
        exact b4e6450
      · have b5e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b5e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b5e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b5e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b5e15 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b5e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b5e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b5e18 : y ≠ (M.op y x) := by grind
        have b5e19 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b5e20 : x ≠ (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b5e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b5e16 (τ X0) X1
             have i₂ := b5e13 X0
             grind)
          | exact superpose b5e13 b5e16
          | exact resolve b5e16 b5e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e23 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b5e11 (σ y) X0 (σ x)
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e11
          | exact resolve b5e11 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e25 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ x)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b5e11 X0 (σ y) (σ x)
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e11
          | exact resolve b5e11 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e26 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X2 (M.op X1 X3)) (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b5e11 X2 (M.op X0 X3) (M.op X1 X3)
             have i₂ := b5e11 X0 X1 X3
             grind)
          | exact superpose b5e11 b5e11
          | exact resolve b5e11 b5e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b5e12 (k (τ X0) X1)
             have i₂ := b5e21 X0 X1
             grind)
          | exact superpose b5e21 b5e12
          | exact resolve b5e12 b5e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e21
        have b5e31 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b5e14 (σ x) (σ y)
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e14
          | (have j0 := b5e14 (σ x) (σ y)
             grind)
          | (have r₁ := b5e14 (σ x) (σ y)
             have r₂ := b5e19
             grind)
          | exact resolve b5e14 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e32 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (k (M.op X1 X2) (M.op X0 X2)) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b5e14 (M.op X1 X2) (M.op X0 X2)
             have i₂ := b5e11 X0 X1 X2
             grind)
          | exact superpose b5e11 b5e14
          | (have j0 := b5e14 (M.op X1 X2) (M.op X0 X2)
             grind)
          | (have r₁ := b5e14 (M.op X1 X1) (M.op X0 X1)
             have r₂ := b5e11 X0 X1 X1
             grind)
          | exact resolve b5e14 b5e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e33 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b5e31
        have b5e34 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (k (M.op X1 X2) (M.op X0 X2)) = (M.op X1 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b5e32 X0 X1 X2
             have i₂ := b5e11 X1 X1 X2
             grind)
          | exact superpose b5e11 b5e32
          | (have j0 := b5e32 X0 X1 X2
             grind)
          | exact resolve b5e32 b5e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e32
        have b5e35 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b5e33
             have i₂ := b5e16 x y
             grind)
          | exact superpose b5e16 b5e33
          | exact resolve b5e33 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e33
        have b5e45 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b5e16 X1 X0
             have i₂ := b5e15 (σ X1) (σ X0)
             grind)
          | exact superpose b5e15 b5e16
          | (have j1 := b5e15 (σ X1) (σ X0)
             grind)
          | exact resolve b5e16 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e52 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ (k x y))) := by
          first
          | (have i₁ := b5e23 (σ x)
             have i₂ := b5e35
             grind)
          | exact superpose b5e35 b5e23
          | exact resolve b5e23 b5e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e53 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (k (M.op X0 (σ x)) (σ y)) = (M.op (M.op X0 (σ x)) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b5e14 (M.op X0 (σ x)) (σ y)
             have i₂ := b5e23 X0
             grind)
          | exact superpose b5e23 b5e14
          | (have j0 := b5e14 X0 (σ y)
             grind)
          | exact resolve b5e14 b5e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e23
        have b5e58 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (k (M.op X0 (σ x)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b5e53 X0
             have i₂ := b5e11 X0 X0 (σ x)
             grind)
          | exact superpose b5e11 b5e53
          | (have j0 := b5e53 X0
             grind)
          | exact resolve b5e53 b5e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e53
        have b5e59 : (σ y) = (M.op (σ y) (σ (k x y))) := by
          first
          | (have i₁ := b5e52
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e52
          | exact resolve b5e52 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e52
        have b5e60 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b5e30 X1 (τ X0)
             have i₂ := b5e13 X0
             grind)
          | exact superpose b5e13 b5e30
          | exact resolve b5e30 b5e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e30
        have b5e70 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b5e14 (σ y) (M.op X0 (σ x))
             have i₂ := b5e25 X0
             grind)
          | exact superpose b5e25 b5e14
          | (have j0 := b5e14 (σ y) (M.op X0 (σ x))
             grind)
          | exact resolve b5e14 b5e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e72 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (M.op X0 (σ y)) (M.op X1 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b5e11 (M.op X0 (σ x)) X1 (σ y)
             have i₂ := b5e25 X0
             grind)
          | exact superpose b5e25 b5e11
          | exact resolve b5e11 b5e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e25
        have b5e73 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 (σ x)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b5e72 X0 X1
             have i₂ := b5e11 X0 X1 (σ y)
             grind)
          | exact superpose b5e11 b5e72
          | exact resolve b5e72 b5e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e72
        have b5e119 : (σ y) = (M.op (σ y) (σ (M.op y x))) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b5e59
             have i₂ := b5e15 x y
             grind)
          | exact superpose b5e15 b5e59
          | (have j1 := b5e15 (σ (M.op y x)) (σ y)
             grind)
          | exact resolve b5e59 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e59
        have b5e128 : (σ y) = (M.op (σ y) (σ (M.op y x))) := by
          first
          | (have r₁ := b5e119
             have r₂ := b5e18
             grind)
          | exact resolve b5e119 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e119
        have b5e171 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (k x y)) X0) := by
          intro X0
          first
          | (have i₁ := b5e73 (σ x) X0
             have i₂ := b5e35
             grind)
          | exact superpose b5e35 b5e73
          | exact resolve b5e73 b5e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e73
        have b5e213 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b5e34 X1 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e34
        have b5e278 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b5e17
             have i₂ := b5e45 x y
             grind)
          | exact superpose b5e45 b5e17
          | (have j1 := b5e45 x y
             grind)
          | exact resolve b5e17 b5e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e286 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b5e14 (σ X0) (σ X1)
             have i₂ := b5e45 X1 X0
             grind)
          | exact superpose b5e45 b5e14
          | (have j0 := b5e14 (σ X0) (σ X1)
             have j1 := b5e45 X1 X0
             grind)
          | (have r₁ := b5e14 (σ X1) (σ X0)
             have r₂ := b5e45 X0 X1
             grind)
          | exact resolve b5e14 b5e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e293 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b5e45 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e295 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b5e286 X0 X1
             have j1 := b5e14 (σ X0) (σ X1)
             grind)
          | (have r₁ := b5e286 X0 X1
             have r₂ := b5e14 (σ X0) (σ X1)
             grind)
          | exact resolve b5e286 b5e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e286
        have b5e300 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b5e295 X0 X1
             have i₂ := b5e16 X0 X1
             grind)
          | exact superpose b5e16 b5e295
          | (have j0 := b5e295 X0 X1
             grind)
          | exact resolve b5e295 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e295
        have b5e326 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ y)) := by
          first
          | (have i₁ := b5e213 (σ x) (σ y)
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e213
          | exact resolve b5e213 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e327 : (σ (k x y)) = (k (σ (k x y)) (σ (k x y))) := by
          first
          | (have i₁ := b5e213 (σ x) (σ x)
             have i₂ := b5e35
             grind)
          | exact superpose b5e35 b5e213
          | exact resolve b5e213 b5e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e345 : (σ (k x y)) = (σ (k (k x y) (k x y))) := by
          first
          | (have i₁ := b5e327
             have i₂ := b5e16 (k x y) (k x y)
             grind)
          | exact superpose b5e16 b5e327
          | exact resolve b5e327 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e327
        have b5e346 : (σ (k x y)) = (k (σ (k x y)) (σ y)) := by
          first
          | (have i₁ := b5e326
             have i₂ := b5e35
             grind)
          | exact superpose b5e35 b5e326
          | exact resolve b5e326 b5e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e326
        have b5e350 : (σ (k x y)) = (σ (k (k x y) y)) := by
          first
          | (have i₁ := b5e346
             have i₂ := b5e16 (k x y) y
             grind)
          | exact superpose b5e16 b5e346
          | exact resolve b5e346 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e346
        have b5e444 : (σ y) ≠ (σ y) ∨ (k (σ (M.op y x)) (σ y)) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by
          first
          | (have i₁ := b5e14 (σ (M.op y x)) (σ y)
             have i₂ := b5e128
             grind)
          | exact superpose b5e128 b5e14
          | (have j0 := b5e14 (σ (M.op y x)) (σ y)
             grind)
          | (have r₁ := b5e14 (σ (M.op y x)) (σ y)
             have r₂ := b5e128
             grind)
          | exact resolve b5e14 b5e128
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e452 : (k (σ (M.op y x)) (σ y)) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by grind
        clear b5e444
        have b5e456 : (σ (k (M.op y x) y)) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by
          first
          | (have i₁ := b5e452
             have i₂ := b5e16 (M.op y x) y
             grind)
          | exact superpose b5e16 b5e452
          | exact resolve b5e452 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e452
        have b5e500 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y x)) X0) ∨ y = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b5e171 X0
             have i₂ := b5e15 x y
             grind)
          | exact superpose b5e15 b5e171
          | (have j1 := b5e15 x y
             grind)
          | exact resolve b5e171 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e171
        have b5e547 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y x)) X0) := by
          intro X0
          first
          | (have j0 := b5e500 X0
             grind)
          | (have r₁ := b5e500 X0
             have r₂ := b5e18
             grind)
          | exact resolve b5e500 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e500
        have b5e668 : (σ (M.op y x)) = (σ (k (M.op y x) y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b5e350
             have i₂ := b5e15 x y
             grind)
          | exact superpose b5e15 b5e350
          | (have j1 := b5e15 x y
             grind)
          | exact resolve b5e350 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e670 : (k (k x y) y) = (τ (σ (k x y))) := by
          first
          | (have i₁ := b5e12 (k (k x y) y)
             have i₂ := b5e350
             grind)
          | exact superpose b5e350 b5e12
          | exact resolve b5e12 b5e350
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e350
        have b5e687 : (k x y) = (k (k x y) y) := by
          first
          | (have i₁ := b5e670
             have i₂ := b5e12 (k x y)
             grind)
          | exact superpose b5e12 b5e670
          | exact resolve b5e670 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e670
        have b5e688 : (σ (M.op y x)) = (σ (k (M.op y x) y)) := by
          first
          | (have r₁ := b5e668
             have r₂ := b5e18
             grind)
          | exact resolve b5e668 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e668
        have b5e1761 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b5e278
             have i₂ := b5e15 y x
             grind)
          | exact superpose b5e15 b5e278
          | (have j1 := b5e15 (σ y) (σ x)
             grind)
          | exact resolve b5e278 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e278
        have b5e1762 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
        clear b5e1761
        have b5e1763 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b5e1762
             have r₂ := b5e20
             grind)
          | exact resolve b5e1762 b5e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1762
        have b5e1766 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b5e17
             have i₂ := b5e1763
             grind)
          | exact superpose b5e1763 b5e17
          | exact resolve b5e17 b5e1763
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e1771 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b5e14 (σ y) (σ x)
             have i₂ := b5e1763
             grind)
          | exact superpose b5e1763 b5e14
          | (have j0 := b5e14 (σ y) (σ x)
             grind)
          | (have r₁ := b5e14 (σ y) (σ x)
             have r₂ := b5e1763
             grind)
          | exact resolve b5e14 b5e1763
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e1775 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op (M.op X0 (σ x)) (M.op X1 (σ x))) := by
          intro X0 X1
          first
          | (have i₁ := b5e26 X1 (σ x) X0 (σ y)
             have i₂ := b5e1763
             grind)
          | exact superpose b5e1763 b5e26
          | exact resolve b5e26 b5e1763
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e26
        have b5e1780 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b5e1771
        have b5e1782 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b5e1775 X0 X1
             have i₂ := b5e11 X0 X1 (σ x)
             grind)
          | exact superpose b5e11 b5e1775
          | exact resolve b5e1775 b5e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1775
        have b5e1785 : (M.op (σ y) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b5e1780
             have i₂ := b5e16 y x
             grind)
          | exact superpose b5e16 b5e1780
          | exact resolve b5e1780 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1780
        have b5e1797 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b5e300 (τ X1) (τ X0)
             have i₂ := b5e60 X0 X1
             grind)
          | exact superpose b5e60 b5e300
          | exact resolve b5e300 b5e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e60 b5e300
        have b5e1812 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b5e1797 X0 X1
             have i₂ := b5e13 (k X0 X1)
             grind)
          | exact superpose b5e13 b5e1797
          | (have j0 := b5e1797 X0 X1
             grind)
          | exact resolve b5e1797 b5e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1797
        have b5e1814 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b5e1812 X0 X1
             have i₂ := b5e13 X1
             grind)
          | exact superpose b5e13 b5e1812
          | (have j0 := b5e1812 X0 X1
             grind)
          | exact resolve b5e1812 b5e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1812
        have b5e1815 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X1 := by
          intro X0 X1
          first
          | (have i₁ := b5e1814 X0 X1
             have i₂ := b5e13 X0
             grind)
          | exact superpose b5e13 b5e1814
          | (have j0 := b5e1814 X0 X1
             grind)
          | exact resolve b5e1814 b5e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1814
        have b5e1816 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b5e1815 X0 X1
             have i₂ := b5e13 (k X0 X1)
             grind)
          | exact superpose b5e13 b5e1815
          | (have j0 := b5e1815 X0 X1
             grind)
          | exact resolve b5e1815 b5e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1815
        have b5e1818 : (σ y) ≠ (σ y) ∨ (M.op (σ (M.op y x)) (σ (M.op y x))) = (k (M.op (σ (M.op y x)) (σ x)) (σ y)) := by
          first
          | (have i₁ := b5e58 (σ (M.op y x))
             have i₂ := b5e128
             grind)
          | exact superpose b5e128 b5e58
          | (have j0 := b5e58 (σ (M.op y x))
             grind)
          | (have r₁ := b5e58 (σ (M.op y x))
             have r₂ := b5e128
             grind)
          | exact resolve b5e58 b5e128
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e58 b5e128
        have b5e1831 : (M.op (σ (M.op y x)) (σ (M.op y x))) = (k (M.op (σ (M.op y x)) (σ x)) (σ y)) := by grind
        clear b5e1818
        have b5e1842 : (k (M.op (σ x) (σ x)) (σ y)) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by
          first
          | (have i₁ := b5e1831
             have i₂ := b5e547 (σ x)
             grind)
          | exact superpose b5e547 b5e1831
          | exact resolve b5e1831 b5e547
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1831
        have b5e1854 : (k (M.op (σ x) (σ x)) (σ y)) = (σ (k (M.op y x) y)) := by
          first
          | (have i₁ := b5e1842
             have i₂ := b5e456
             grind)
          | exact superpose b5e456 b5e1842
          | exact resolve b5e1842 b5e456
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e456 b5e1842
        have b5e1860 : (σ (M.op y x)) = (k (M.op (σ x) (σ x)) (σ y)) := by
          first
          | (have i₁ := b5e1854
             have i₂ := b5e688
             grind)
          | exact superpose b5e688 b5e1854
          | exact resolve b5e1854 b5e688
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e688 b5e1854
        have b5e1863 : (σ (M.op y x)) = (k (σ (k x y)) (σ y)) := by
          first
          | (have i₁ := b5e1860
             have i₂ := b5e35
             grind)
          | exact superpose b5e35 b5e1860
          | exact resolve b5e1860 b5e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e35 b5e1860
        have b5e1865 : (σ (M.op y x)) = (σ (k (k x y) y)) := by
          first
          | (have i₁ := b5e1863
             have i₂ := b5e16 (k x y) y
             grind)
          | exact superpose b5e16 b5e1863
          | exact resolve b5e1863 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1863
        have b5e1867 : (σ (k x y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b5e1865
             have i₂ := b5e687
             grind)
          | exact superpose b5e687 b5e1865
          | exact resolve b5e1865 b5e687
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e687 b5e1865
        have b5e1880 : (k x y) = (τ (σ (M.op y x))) := by
          first
          | (have i₁ := b5e12 (k x y)
             have i₂ := b5e1867
             grind)
          | exact superpose b5e1867 b5e12
          | exact resolve b5e12 b5e1867
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1867
        have b5e1909 : (M.op y x) = (k x y) := by
          first
          | (have i₁ := b5e1880
             have i₂ := b5e12 (M.op y x)
             grind)
          | exact superpose b5e12 b5e1880
          | exact resolve b5e1880 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1880
        have b5e3331 : (σ (k y x)) = (σ (k y y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b5e45 y y
             have i₂ := b5e1785
             grind)
          | exact superpose b5e1785 b5e45
          | exact resolve b5e45 b5e1785
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e45
        have b5e3339 : (σ y) ≠ (σ (k y x)) ∨ (σ (k y x)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b5e14 (σ y) (σ y)
             have i₂ := b5e1785
             grind)
          | exact superpose b5e1785 b5e14
          | exact resolve b5e14 b5e1785
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1785
        have b5e3361 : (σ (k y x)) = (σ (k y y)) ∨ (σ y) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b5e3339
             have i₂ := b5e16 y y
             grind)
          | exact superpose b5e16 b5e3339
          | exact resolve b5e3339 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e3339
        have b5e3371 : (σ (k y x)) = (σ (k y y)) := by
          first
          | (have r₁ := b5e3361
             have r₂ := b5e3331
             grind)
          | exact resolve b5e3361 b5e3331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e3331 b5e3361
        have b5e3899 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b5e3371
             have i₂ := b5e15 y x
             grind)
          | exact superpose b5e15 b5e3371
          | (have j1 := b5e15 y x
             grind)
          | exact resolve b5e3371 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e3903 : (k y x) = (τ (σ (k y y))) := by
          first
          | (have i₁ := b5e12 (k y x)
             have i₂ := b5e3371
             grind)
          | exact superpose b5e3371 b5e12
          | exact resolve b5e12 b5e3371
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e3371
        have b5e3930 : (k y x) = (k y y) := by
          first
          | (have i₁ := b5e3903
             have i₂ := b5e12 (k y y)
             grind)
          | exact superpose b5e12 b5e3903
          | exact resolve b5e3903 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e3903
        have b5e3932 : (σ (M.op x y)) = (σ (k y y)) := by
          first
          | (have r₁ := b5e3899
             have r₂ := b5e20
             grind)
          | exact resolve b5e3899 b5e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e3899
        have b5e4443 : (M.op x y) = (k y y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b5e15 y x
             have i₂ := b5e3930
             grind)
          | exact superpose b5e3930 b5e15
          | (have j0 := b5e15 y x
             grind)
          | exact resolve b5e15 b5e3930
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e3930
        have b5e4444 : (M.op x y) = (k y y) := by
          first
          | (have r₁ := b5e4443
             have r₂ := b5e20
             grind)
          | exact resolve b5e4443 b5e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e4443
        have b5e5181 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b5e15 y y
             have i₂ := b5e4444
             grind)
          | exact superpose b5e4444 b5e15
          | (have j0 := b5e15 y y
             grind)
          | exact resolve b5e15 b5e4444
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e4444
        have b5e5610 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b5e70 (σ y)
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e70
          | exact resolve b5e70 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e70
        have b5e5630 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have j1 := b5e15 (σ y) (σ y)
             grind)
          | (have r₁ := b5e5610
             have r₂ := b5e15 (σ y) (σ y)
             grind)
          | exact resolve b5e5610 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e5610
        have b5e5632 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b5e5630
             have i₂ := b5e16 y y
             grind)
          | exact superpose b5e16 b5e5630
          | exact resolve b5e5630 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e5630
        have b5e5634 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b5e5632
             have i₂ := b5e3932
             grind)
          | exact superpose b5e3932 b5e5632
          | exact resolve b5e5632 b5e3932
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e3932 b5e5632
        have b5e5643 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
          intro X0
          first
          | (have i₁ := b5e1782 X0 (σ y)
             have i₂ := b5e5634
             grind)
          | exact superpose b5e5634 b5e1782
          | exact resolve b5e1782 b5e5634
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1782 b5e5634
        have b5e19849 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y y) (M.op X0 y)) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b5e11 x X0 y
             have i₂ := b5e5181
             grind)
          | exact superpose b5e5181 b5e11
          | exact resolve b5e11 b5e5181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e19850 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 y) (M.op y y)) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b5e11 X0 x y
             have i₂ := b5e5181
             grind)
          | exact superpose b5e5181 b5e11
          | exact resolve b5e11 b5e5181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e5181
        have b5e19909 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b5e19850 X0
             have i₂ := b5e11 X0 y y
             grind)
          | exact superpose b5e11 b5e19850
          | exact resolve b5e19850 b5e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e19850
        have b5e19910 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b5e19849 X0
             have i₂ := b5e11 y X0 y
             grind)
          | exact superpose b5e11 b5e19849
          | exact resolve b5e19849 b5e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e19849
        have b5e24681 : (τ (σ (k x y))) = (k (k x y) (k x y)) := by
          first
          | (have i₁ := b5e12 (k (k x y) (k x y))
             have i₂ := b5e345
             grind)
          | exact superpose b5e345 b5e12
          | exact resolve b5e12 b5e345
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e345
        have b5e24729 : (τ (σ (M.op y x))) = (k (M.op y x) (M.op y x)) := by
          first
          | (have i₁ := b5e24681
             have i₂ := b5e1909
             grind)
          | exact superpose b5e1909 b5e24681
          | exact resolve b5e24681 b5e1909
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e24681
        have b5e24759 : (M.op y x) = (k (M.op y x) (M.op y x)) := by
          first
          | (have i₁ := b5e24729
             have i₂ := b5e12 (M.op y x)
             grind)
          | exact superpose b5e12 b5e24729
          | exact resolve b5e24729 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e24729
        have b5e24820 : (M.op y x) ≠ (M.op y x) ∨ (M.op y x) = (M.op (M.op y x) (M.op y x)) := by
          first
          | (have i₁ := b5e1816 (M.op y x) (M.op y x)
             have i₂ := b5e24759
             grind)
          | exact superpose b5e24759 b5e1816
          | (have r₁ := b5e1816 (M.op y x) (M.op y x)
             have r₂ := b5e24759
             grind)
          | exact resolve b5e1816 b5e24759
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1816 b5e24759
        have b5e24821 : (M.op y x) = (M.op (M.op y x) (M.op y x)) := by grind
        clear b5e24820
        have b5e24827 : (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b5e24821
             have i₂ := b5e11 y y x
             grind)
          | exact superpose b5e11 b5e24821
          | exact resolve b5e24821 b5e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e24821
        have b5e25099 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b5e18
             have i₂ := b5e24827
             grind)
          | exact superpose b5e24827 b5e18
          | exact resolve b5e18 b5e24827
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e25105 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y y)) X0) := by
          intro X0
          first
          | (have i₁ := b5e547 X0
             have i₂ := b5e24827
             grind)
          | exact superpose b5e24827 b5e547
          | exact resolve b5e547 b5e24827
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e547
        have b5e25112 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y y) (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b5e11 y X0 x
             have i₂ := b5e24827
             grind)
          | exact superpose b5e24827 b5e11
          | exact resolve b5e11 b5e24827
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e25114 : y ≠ (M.op y y) ∨ (k x y) = (M.op x x) := by
          first
          | (have i₁ := b5e14 x y
             have i₂ := b5e24827
             grind)
          | exact superpose b5e24827 b5e14
          | (have j0 := b5e14 y y
             grind)
          | exact resolve b5e14 b5e24827
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e25146 : (M.op x x) = (k (M.op x x) (M.op y y)) := by
          first
          | (have i₁ := b5e213 x y
             have i₂ := b5e24827
             grind)
          | exact superpose b5e24827 b5e213
          | exact resolve b5e213 b5e24827
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e213
        have b5e25175 : (M.op y x) = (M.op x x) ∨ y ≠ (M.op y y) := by
          first
          | (have i₁ := b5e25114
             have i₂ := b5e1909
             grind)
          | exact superpose b5e1909 b5e25114
          | exact resolve b5e25114 b5e1909
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1909 b5e25114
        have b5e25197 : (M.op y x) = (M.op x x) := by
          first
          | (have j1 := b5e19910 x
             grind)
          | (have r₁ := b5e25175
             have r₂ := b5e19910 x
             grind)
          | exact resolve b5e25175 b5e19910
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e19910 b5e25175
        have b5e25212 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b5e25197
             have i₂ := b5e24827
             grind)
          | exact superpose b5e24827 b5e25197
          | exact resolve b5e25197 b5e24827
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e24827 b5e25197
        have b5e25527 : ∀ X0 : G, y ≠ y ∨ (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b5e25099
             have i₂ := b5e19909 X0
             grind)
          | exact superpose b5e19909 b5e25099
          | (have j1 := b5e19909 X0
             grind)
          | (have r₁ := b5e25099
             have r₂ := b5e19909 X0
             grind)
          | exact resolve b5e25099 b5e19909
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e19909 b5e25099
        have b5e25528 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b5e25527 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e25527
        have b5e26258 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y y) (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b5e11 x X0 x
             have i₂ := b5e25212
             grind)
          | exact superpose b5e25212 b5e11
          | exact resolve b5e11 b5e25212
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e25212
        have b5e26327 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b5e26258 X0
             have i₂ := b5e25112 X0
             grind)
          | exact superpose b5e25112 b5e26258
          | exact resolve b5e26258 b5e25112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e25112 b5e26258
        have b5e26603 : (σ x) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b5e1766
             have i₂ := b5e26327 y
             grind)
          | exact superpose b5e26327 b5e1766
          | exact resolve b5e1766 b5e26327
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1766
        have b5e31213 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op x x))) := by
          first
          | (have i₁ := b5e293 (M.op y y) (M.op x x)
             have i₂ := b5e25146
             grind)
          | exact superpose b5e25146 b5e293
          | (have j0 := b5e293 (M.op y y) (M.op x x)
             grind)
          | exact resolve b5e293 b5e25146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e293 b5e25146
        have b5e31223 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op x x))) := by
          first
          | (have i₁ := b5e31213
             have i₂ := b5e25528 x
             grind)
          | exact superpose b5e25528 b5e31213
          | exact resolve b5e31213 b5e25528
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e31213
        have b5e31247 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op x x))) := by
          first
          | (have i₁ := b5e31223
             have i₂ := b5e26327 y
             grind)
          | exact superpose b5e26327 b5e31223
          | exact resolve b5e31223 b5e26327
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e26327 b5e31223
        have b5e31248 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op x x))) := by grind
        clear b5e31247
        have b5e31260 : (σ (M.op y y)) = (M.op (σ x) (σ (M.op x x))) := by
          first
          | (have i₁ := b5e31248
             have i₂ := b5e25105 (σ (M.op x x))
             grind)
          | exact superpose b5e25105 b5e31248
          | exact resolve b5e31248 b5e25105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e25105 b5e31248
        have b5e31270 : (σ (M.op y y)) = (M.op (σ x) (σ (M.op x y))) := by
          first
          | (have i₁ := b5e31260
             have i₂ := b5e25528 x
             grind)
          | exact superpose b5e25528 b5e31260
          | exact resolve b5e31260 b5e25528
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e25528 b5e31260
        have b5e31279 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b5e31270
             have i₂ := b5e5643 (σ x)
             grind)
          | exact superpose b5e5643 b5e31270
          | exact resolve b5e31270 b5e5643
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e5643 b5e31270
        have b5e31287 : (σ x) = (σ (M.op y y)) := by
          first
          | (have i₁ := b5e31279
             have i₂ := b5e1763
             grind)
          | exact superpose b5e1763 b5e31279
          | exact resolve b5e31279 b5e1763
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1763 b5e31279
        have b5e31294 : False := by grind
        exact b5e31294
    · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
      · have b6e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b6e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e18 : y ≠ (M.op y x) := by grind
        have b6e19 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b6e20 : x = (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b6e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e17
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e17
          | exact resolve b6e17 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 (τ X0) X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e16
          | exact resolve b6e16 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X1 (τ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e16
          | exact resolve b6e16 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X1 X2))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e11 (M.op X0 X2) X3 (M.op X1 X2)
             have i₂ := b6e11 X0 X1 X2
             grind)
          | exact superpose b6e11 b6e11
          | exact resolve b6e11 b6e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e26 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 y) x) := by
          intro X0
          first
          | (have i₁ := b6e11 X0 x y
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e11
          | exact resolve b6e11 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e32 : x ≠ x ∨ (k y x) = (M.op y y) := by
          first
          | (have i₁ := b6e14 y x
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e14
          | (have j0 := b6e14 y x
             grind)
          | (have r₁ := b6e14 y x
             have r₂ := b6e20
             grind)
          | exact resolve b6e14 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e34 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (k (M.op X1 X2) (M.op X0 X2)) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e14 (M.op X1 X2) (M.op X0 X2)
             have i₂ := b6e11 X0 X1 X2
             grind)
          | exact superpose b6e11 b6e14
          | (have j0 := b6e14 (M.op X1 X2) (M.op X0 X2)
             grind)
          | (have r₁ := b6e14 (M.op X1 X1) (M.op X0 X1)
             have r₂ := b6e11 X0 X1 X1
             grind)
          | exact resolve b6e14 b6e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e35 : (k y x) = (M.op y y) := by grind
        clear b6e32
        have b6e36 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (k (M.op X1 X2) (M.op X0 X2)) = (M.op X1 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e34 X0 X1 X2
             have i₂ := b6e11 X1 X1 X2
             grind)
          | exact superpose b6e11 b6e34
          | (have j0 := b6e34 X0 X1 X2
             grind)
          | exact resolve b6e34 b6e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X1 X0
             have i₂ := b6e15 (σ X1) (σ X0)
             grind)
          | exact superpose b6e15 b6e16
          | (have j1 := b6e15 (σ X1) (σ X0)
             grind)
          | exact resolve b6e16 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e43 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op (M.op X1 x) (M.op X0 x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e11 X1 (M.op X0 y) x
             have i₂ := b6e26 X0
             grind)
          | exact superpose b6e26 b6e11
          | exact resolve b6e11 b6e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e44 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op X0 x) (M.op X1 x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e11 (M.op X0 y) X1 x
             have i₂ := b6e26 X0
             grind)
          | exact superpose b6e26 b6e11
          | exact resolve b6e11 b6e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e45 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e44 X0 X1
             have i₂ := b6e11 X0 X1 x
             grind)
          | exact superpose b6e11 b6e44
          | exact resolve b6e44 b6e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e46 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e43 X0 X1
             have i₂ := b6e11 X1 X0 x
             grind)
          | exact superpose b6e11 b6e43
          | exact resolve b6e43 b6e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e51 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (k (τ X0) X1)
             have i₂ := b6e22 X0 X1
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e22
        have b6e54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 y) ∨ (M.op X1 X1) = (k X1 (M.op X0 y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e14 X1 (M.op X0 y)
             have i₂ := b6e45 X0 X1
             grind)
          | exact superpose b6e45 b6e14
          | (have j0 := b6e14 X1 (M.op X0 y)
             grind)
          | (have r₁ := b6e14 y (M.op X0 y)
             have r₂ := b6e45 X0 y
             grind)
          | exact resolve b6e14 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e65 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (k X0 (τ X1))
             have i₂ := b6e23 X1 X0
             grind)
          | exact superpose b6e23 b6e12
          | exact resolve b6e12 b6e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e100 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op X2 (M.op y X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e45 X0 (M.op X2 (M.op y X1))
             have i₂ := b6e25 X0 y X1 X2
             grind)
          | exact superpose b6e25 b6e45
          | exact resolve b6e45 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e121 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e51 X1 (τ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e51
          | exact resolve b6e51 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e185 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e65 X1 X0
             have i₂ := b6e15 (σ X1) X0
             grind)
          | exact superpose b6e15 b6e65
          | (have j1 := b6e15 (σ X1) X0
             grind)
          | exact resolve b6e65 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e210 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b6e36 X1 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e250 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ (k X0 X1)) (M.op X2 (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e11 (σ X1) X2 (σ X0)
             have i₂ := b6e40 X1 X0
             grind)
          | exact superpose b6e40 b6e11
          | (have j1 := b6e40 X1 X0
             grind)
          | exact resolve b6e11 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e252 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e14 (σ X0) (σ X1)
             have i₂ := b6e40 X1 X0
             grind)
          | exact superpose b6e40 b6e14
          | (have j0 := b6e14 (σ X0) (σ X1)
             have j1 := b6e40 X1 X0
             grind)
          | (have r₁ := b6e14 (σ X1) (σ X0)
             have r₂ := b6e40 X0 X1
             grind)
          | exact resolve b6e14 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e259 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e40 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e261 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b6e252 X0 X1
             have j1 := b6e14 (σ X0) (σ X1)
             grind)
          | (have r₁ := b6e252 X0 X1
             have r₂ := b6e14 (σ X0) (σ X1)
             grind)
          | exact resolve b6e252 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e252
        have b6e264 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e261 X0 X1
             have i₂ := b6e16 X0 X1
             grind)
          | exact superpose b6e16 b6e261
          | (have j0 := b6e261 X0 X1
             grind)
          | exact resolve b6e261 b6e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e261
        have b6e892 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e259 (τ X1) (τ X0)
             have i₂ := b6e121 X1 X0
             grind)
          | exact superpose b6e121 b6e259
          | (have j0 := b6e259 (τ X1) (τ X0)
             grind)
          | exact resolve b6e259 b6e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e895 : (σ x) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e259 x y
             have i₂ := b6e35
             grind)
          | exact superpose b6e35 b6e259
          | (have j0 := b6e259 x y
             grind)
          | exact resolve b6e259 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e259
        have b6e900 : (σ x) ≠ (σ (M.op y y)) := by
          first
          | (have r₁ := b6e895
             have r₂ := b6e21
             grind)
          | exact resolve b6e895 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e895
        have b6e901 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e892 X0 X1
             have i₂ := b6e13 (k X0 X1)
             grind)
          | exact superpose b6e13 b6e892
          | (have j0 := b6e892 X0 X1
             grind)
          | exact resolve b6e892 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e892
        have b6e903 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e901 X0 X1
             have i₂ := b6e13 X1
             grind)
          | exact superpose b6e13 b6e901
          | (have j0 := b6e901 X0 X1
             grind)
          | exact resolve b6e901 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e901
        have b6e904 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e903 X0 X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e903
          | (have j0 := b6e903 X0 X1
             grind)
          | exact resolve b6e903 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e903
        have b6e905 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e904 X0 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e904
          | (have j0 := b6e904 X0 X1
             grind)
          | exact resolve b6e904 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e904
        have b6e3273 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y y)) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e250 y x X0
             have i₂ := b6e35
             grind)
          | exact superpose b6e35 b6e250
          | (have j0 := b6e250 y x x
             grind)
          | exact resolve b6e250 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35 b6e250
        have b6e3365 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y y)) (M.op X0 (σ y))) := by
          intro X0
          first
          | (have j0 := b6e3273 X0
             grind)
          | (have r₁ := b6e3273 X0
             have r₂ := b6e21
             grind)
          | exact resolve b6e3273 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e21 b6e3273
        have b6e3404 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ (M.op y y))) = (M.op X0 (M.op (σ x) y)) := by
          intro X0
          first
          | (have i₁ := b6e100 X0 (σ y) (σ (M.op y y))
             have i₂ := b6e3365 y
             grind)
          | exact superpose b6e3365 b6e100
          | exact resolve b6e100 b6e3365
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e100
        have b6e3408 : ∀ X0 X1 : G, (M.op (σ (M.op y y)) X1) = (M.op (M.op (σ x) X0) (M.op X1 (M.op X0 (σ y)))) := by
          intro X0 X1
          first
          | (have i₁ := b6e11 (σ (M.op y y)) X1 (M.op X0 (σ y))
             have i₂ := b6e3365 X0
             grind)
          | exact superpose b6e3365 b6e11
          | exact resolve b6e11 b6e3365
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3365
        have b6e3452 : ∀ X1 : G, (M.op (σ (M.op y y)) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
          intro X1
          first
          | (have i₁ := b6e3408 x X1
             have i₂ := b6e25 (σ x) x (σ y) X1
             grind)
          | exact superpose b6e25 b6e3408
          | exact resolve b6e3408 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25 b6e3408
        have b6e3455 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ (M.op y y))) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e3404 X0
             have i₂ := b6e46 (σ x) X0
             grind)
          | exact superpose b6e46 b6e3404
          | exact resolve b6e3404 b6e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3404
        have b6e4750 : (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e3452 (σ (M.op y y))
             have i₂ := b6e3455 (σ x)
             grind)
          | exact superpose b6e3455 b6e3452
          | exact resolve b6e3452 b6e3455
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3452
        have b6e9869 : (M.op (σ x) (σ x)) = (σ (k (M.op y y) (M.op y y))) ∨ (σ (M.op y y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e40 (M.op y y) (M.op y y)
             have i₂ := b6e4750
             grind)
          | exact superpose b6e4750 b6e40
          | exact resolve b6e40 b6e4750
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4750
        have b6e9934 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op y y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e9869
             have i₂ := b6e210 y y
             grind)
          | exact superpose b6e210 b6e9869
          | exact resolve b6e9869 b6e210
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9869
        have b6e9935 : (σ (M.op y y)) = (M.op (σ x) (σ x)) := by grind
        clear b6e9934
        have b6e10283 : (σ (M.op y y)) = (σ (k x x)) ∨ (σ x) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e40 x x
             have i₂ := b6e9935
             grind)
          | exact superpose b6e9935 b6e40
          | exact resolve b6e40 b6e9935
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e10291 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y y)) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b6e11 (σ x) X0 (σ x)
             have i₂ := b6e9935
             grind)
          | exact superpose b6e9935 b6e11
          | exact resolve b6e11 b6e9935
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e10349 : (σ (M.op y y)) = (σ (k x x)) := by
          first
          | (have r₁ := b6e10283
             have r₂ := b6e900
             grind)
          | exact resolve b6e10283 b6e900
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e10283
        have b6e10736 : (k x x) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e12 (k x x)
             have i₂ := b6e10349
             grind)
          | exact superpose b6e10349 b6e12
          | exact resolve b6e12 b6e10349
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e10778 : (M.op y y) = (k x x) := by
          first
          | (have i₁ := b6e10736
             have i₂ := b6e12 (M.op y y)
             grind)
          | exact superpose b6e12 b6e10736
          | exact resolve b6e10736 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e10736
        have b6e10843 : (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e15 x x
             have i₂ := b6e10778
             grind)
          | exact superpose b6e10778 b6e15
          | (have j0 := b6e15 x x
             grind)
          | exact resolve b6e15 b6e10778
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e10848 : x ≠ (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e905 x x
             have i₂ := b6e10778
             grind)
          | exact superpose b6e10778 b6e905
          | (have j0 := b6e905 x x
             grind)
          | exact resolve b6e905 b6e10778
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e905 b6e10778
        have b6e12769 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y y) (M.op X0 x)) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b6e11 x X0 x
             have i₂ := b6e10843
             grind)
          | exact superpose b6e10843 b6e11
          | exact resolve b6e11 b6e10843
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e10843
        have b6e12831 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 x)) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b6e12769 X0
             have i₂ := b6e45 y (M.op X0 x)
             grind)
          | exact superpose b6e45 b6e12769
          | exact resolve b6e12769 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45 b6e12769
        have b6e16618 : ∀ X0 : G, (M.op y y) = (k y (M.op X0 y)) := by
          intro X0
          first
          | (have j0 := b6e54 X0 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e16726 : ∀ X0 : G, (σ (M.op y y)) ≠ (σ (M.op X0 y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e264 y (M.op X0 y)
             have i₂ := b6e16618 X0
             grind)
          | exact superpose b6e16618 b6e264
          | exact resolve b6e264 b6e16618
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e264 b6e16618
        have b6e16737 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e185 X0 (τ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e185
          | exact resolve b6e185 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e185
        have b6e16782 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e16737 X0 X1
             have i₂ := b6e121 X1 X0
             grind)
          | exact superpose b6e121 b6e16737
          | (have j0 := b6e16737 X0 X1
             grind)
          | exact resolve b6e16737 b6e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e121 b6e16737
        have b6e18558 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e16782 (σ X0) (σ X1)
             have i₂ := b6e16 X0 X1
             grind)
          | exact superpose b6e16 b6e16782
          | (have j0 := b6e16782 (σ X0) (σ X1)
             grind)
          | exact resolve b6e16782 b6e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e16782
        have b6e18613 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18558 X0 X1
             have i₂ := b6e12 (k X0 X1)
             grind)
          | exact superpose b6e12 b6e18558
          | (have j0 := b6e18558 X0 X1
             grind)
          | exact resolve b6e18558 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e18558
        have b6e19153 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
          first
          | (have i₁ := b6e10291 (σ x)
             have i₂ := b6e9935
             grind)
          | exact superpose b6e9935 b6e10291
          | exact resolve b6e10291 b6e9935
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9935 b6e10291
        have b6e540483 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e16726
        have b6e540501 : (M.op (σ y) (σ x)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
          first
          | (have i₁ := b6e3455 (σ y)
             have i₂ := b6e540483
             grind)
          | exact superpose b6e540483 b6e3455
          | exact resolve b6e3455 b6e540483
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3455 b6e540483
        have b6e540767 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e540501
             have i₂ := b6e19153
             grind)
          | exact superpose b6e19153 b6e540501
          | exact resolve b6e540501 b6e19153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e19153 b6e540501
        have b6e540890 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e540767
             grind)
          | exact superpose b6e540767 b6e19
          | exact resolve b6e19 b6e540767
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e540893 : (k x y) = (τ (σ (M.op y y))) ∨ (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e18613 x y
             have i₂ := b6e540767
             grind)
          | exact superpose b6e540767 b6e18613
          | exact resolve b6e18613 b6e540767
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e18613 b6e540767
        have b6e540956 : (M.op y y) = (k x y) ∨ (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e540893
             have i₂ := b6e12 (M.op y y)
             grind)
          | exact superpose b6e12 b6e540893
          | exact resolve b6e540893 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e540893
        have b6e540968 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b6e540956
             have r₂ := b6e540890
             grind)
          | exact resolve b6e540956 b6e540890
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e540890 b6e540956
        have b6e541034 : (M.op y x) = (M.op y y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e15 x y
             have i₂ := b6e540968
             grind)
          | exact superpose b6e540968 b6e15
          | (have j0 := b6e15 x y
             grind)
          | exact resolve b6e15 b6e540968
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e540968
        have b6e541094 : (M.op y x) = (M.op y y) := by
          first
          | (have r₁ := b6e541034
             have r₂ := b6e18
             grind)
          | exact resolve b6e541034 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e541034
        have b6e541206 : (M.op x y) = (M.op y (M.op y y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e12831 y
             have i₂ := b6e541094
             grind)
          | exact superpose b6e541094 b6e12831
          | exact resolve b6e12831 b6e541094
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e12831 b6e541094
        have b6e541316 : (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e541206
             have i₂ := b6e46 y y
             grind)
          | exact superpose b6e46 b6e541206
          | exact resolve b6e541206 b6e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46 b6e541206
        have b6e541343 : x = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e541316
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e541316
          | exact resolve b6e541316 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e541316
        have b6e541359 : x = (M.op x x) := by
          first
          | (have r₁ := b6e541343
             have r₂ := b6e10848
             grind)
          | exact resolve b6e541343 b6e10848
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e10848 b6e541343
        have b6e541625 : x = (k x x) := by
          first
          | (have i₁ := b6e210 x x
             have i₂ := b6e541359
             grind)
          | exact superpose b6e541359 b6e210
          | exact resolve b6e210 b6e541359
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e210 b6e541359
        have b6e541766 : (σ x) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e10349
             have i₂ := b6e541625
             grind)
          | exact superpose b6e541625 b6e10349
          | exact resolve b6e10349 b6e541625
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e10349 b6e541625
        have b6e541827 : False := by grind
        exact b6e541827
      · have b7e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b7e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b7e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b7e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b7e15 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b7e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b7e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b7e18 : y ≠ (M.op y x) := by grind
        have b7e19 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b7e20 : x ≠ (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b7e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e16 (τ X0) X1
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e16
          | exact resolve b7e16 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X1 X2))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e11 (M.op X0 X2) X3 (M.op X1 X2)
             have i₂ := b7e11 X0 X1 X2
             grind)
          | exact superpose b7e11 b7e11
          | exact resolve b7e11 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X2 (M.op X1 X3)) (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e11 X2 (M.op X0 X3) (M.op X1 X3)
             have i₂ := b7e11 X0 X1 X3
             grind)
          | exact superpose b7e11 b7e11
          | exact resolve b7e11 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b7e12 (k (τ X0) X1)
             have i₂ := b7e21 X0 X1
             grind)
          | exact superpose b7e21 b7e12
          | exact resolve b7e12 b7e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e21
        have b7e29 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (k (M.op X1 X2) (M.op X0 X2)) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e14 (M.op X1 X2) (M.op X0 X2)
             have i₂ := b7e11 X0 X1 X2
             grind)
          | exact superpose b7e11 b7e14
          | (have j0 := b7e14 (M.op X1 X2) (M.op X0 X2)
             grind)
          | (have r₁ := b7e14 (M.op X1 X1) (M.op X0 X1)
             have r₂ := b7e11 X0 X1 X1
             grind)
          | exact resolve b7e14 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e30 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (k (M.op X1 X2) (M.op X0 X2)) = (M.op X1 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e29 X0 X1 X2
             have i₂ := b7e11 X1 X1 X2
             grind)
          | exact superpose b7e11 b7e29
          | (have j0 := b7e29 X0 X1 X2
             grind)
          | exact resolve b7e29 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e29
        have b7e40 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e16 X1 X0
             have i₂ := b7e15 (σ X1) (σ X0)
             grind)
          | exact superpose b7e15 b7e16
          | (have j1 := b7e15 (σ X1) (σ X0)
             grind)
          | exact resolve b7e16 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b7e28 X1 (τ X0)
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e28
          | exact resolve b7e28 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e54 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X1 X3)) X4) = (M.op (M.op X2 (M.op X0 X3)) (M.op X4 (M.op X0 X1))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b7e23 X2 (M.op X0 X3) (M.op X1 X3) X4
             have i₂ := b7e11 X0 X1 X3
             grind)
          | exact superpose b7e11 b7e23
          | exact resolve b7e23 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e81 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X1 X5))) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X4 (M.op X0 (M.op X5 X2)))) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b7e24 X4 (M.op X0 (M.op X5 X2)) X3 (M.op X1 X5)
             have i₂ := b7e24 X1 X5 X0 X2
             grind)
          | exact superpose b7e24 b7e24
          | exact resolve b7e24 b7e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e101 : ∀ X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X1 X5))) = (M.op (M.op X3 (M.op (M.op X5 X2) (M.op X1 X2))) X4) := by
          intro X1 X2 X3 X4 X5
          first
          | (have i₁ := b7e81 x X1 X2 X3 X4 X5
             have i₂ := b7e54 x (M.op X5 X2) X3 (M.op X1 X2) X4
             grind)
          | exact superpose b7e54 b7e81
          | exact resolve b7e81 b7e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e54 b7e81
        have b7e102 : ∀ X1 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X1 X5))) = (M.op (M.op X3 (M.op X5 X1)) X4) := by
          intro X1 X3 X4 X5
          first
          | (have i₁ := b7e101 X1 x X3 X4 X5
             have i₂ := b7e11 X5 X1 x
             grind)
          | exact superpose b7e11 b7e101
          | exact resolve b7e101 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e101
        have b7e121 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b7e30 X1 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e30
        have b7e145 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e40 x y
             grind)
          | exact superpose b7e40 b7e17
          | (have j1 := b7e40 x y
             grind)
          | exact resolve b7e17 b7e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e146 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ (k X0 X1)) (M.op X2 (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e11 (σ X1) X2 (σ X0)
             have i₂ := b7e40 X1 X0
             grind)
          | exact superpose b7e40 b7e11
          | (have j1 := b7e40 X1 X0
             grind)
          | exact resolve b7e11 b7e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e148 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b7e14 (σ X0) (σ X1)
             have i₂ := b7e40 X1 X0
             grind)
          | exact superpose b7e40 b7e14
          | (have j0 := b7e14 (σ X0) (σ X1)
             have j1 := b7e40 X1 X0
             grind)
          | (have r₁ := b7e14 (σ X1) (σ X0)
             have r₂ := b7e40 X0 X1
             grind)
          | exact resolve b7e14 b7e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e157 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b7e40 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e159 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b7e148 X0 X1
             have j1 := b7e14 (σ X0) (σ X1)
             grind)
          | (have r₁ := b7e148 X0 X1
             have r₂ := b7e14 (σ X0) (σ X1)
             grind)
          | exact resolve b7e148 b7e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e148
        have b7e162 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b7e159 X0 X1
             have i₂ := b7e16 X0 X1
             grind)
          | exact superpose b7e16 b7e159
          | (have j0 := b7e159 X0 X1
             grind)
          | exact resolve b7e159 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e159
        have b7e274 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 (M.op X2 X3)) (M.op X3 X2))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e11 X0 X1 (M.op X2 X3)
             have i₂ := b7e102 X3 X0 (M.op X1 (M.op X2 X3)) X2
             grind)
          | exact superpose b7e102 b7e11
          | exact resolve b7e11 b7e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e306 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X3 X3))) := by
          intro X0 X1 X3
          first
          | (have i₁ := b7e274 X0 X1 x X3
             have i₂ := b7e24 X3 x X1 X3
             grind)
          | exact superpose b7e24 b7e274
          | exact resolve b7e274 b7e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e274
        have b7e401 : ∀ X0 X1 : G, (σ (M.op X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ (M.op X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b7e157 (M.op X1 X0) (M.op X0 X0)
             have i₂ := b7e121 X0 X1
             grind)
          | exact superpose b7e121 b7e157
          | (have j0 := b7e157 (M.op X1 X0) (M.op X0 X0)
             grind)
          | exact resolve b7e157 b7e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e406 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b7e157 (τ X1) (τ X0)
             have i₂ := b7e43 X1 X0
             grind)
          | exact superpose b7e43 b7e157
          | (have j0 := b7e157 (τ X1) (τ X0)
             grind)
          | exact resolve b7e157 b7e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e413 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b7e406 X0 X1
             have i₂ := b7e13 (k X0 X1)
             grind)
          | exact superpose b7e13 b7e406
          | (have j0 := b7e406 X0 X1
             grind)
          | exact resolve b7e406 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e406
        have b7e415 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b7e413 X0 X1
             have i₂ := b7e13 X1
             grind)
          | exact superpose b7e13 b7e413
          | (have j0 := b7e413 X0 X1
             grind)
          | exact resolve b7e413 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e413
        have b7e416 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e415 X0 X1
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e415
          | (have j0 := b7e415 X0 X1
             grind)
          | exact resolve b7e415 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e415
        have b7e417 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e416 X0 X0
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e416
          | (have j0 := b7e416 X0 X1
             grind)
          | exact resolve b7e416 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e416
        have b7e424 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b7e417 (τ X0) (τ X1)
             have i₂ := b7e43 X1 X0
             grind)
          | exact superpose b7e43 b7e417
          | (have j0 := b7e417 (τ X0) (τ X1)
             grind)
          | exact resolve b7e417 b7e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e417
        have b7e508 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b7e145
             have i₂ := b7e15 y x
             grind)
          | exact superpose b7e15 b7e145
          | (have j1 := b7e15 (σ y) (σ x)
             grind)
          | exact resolve b7e145 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e145
        have b7e509 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
        clear b7e508
        have b7e510 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b7e509
             have r₂ := b7e20
             grind)
          | exact resolve b7e509 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e509
        have b7e515 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b7e14 (σ y) (σ x)
             have i₂ := b7e510
             grind)
          | exact superpose b7e510 b7e14
          | (have j0 := b7e14 (σ y) (σ x)
             grind)
          | (have r₁ := b7e14 (σ y) (σ x)
             have r₂ := b7e510
             grind)
          | exact resolve b7e14 b7e510
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e517 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (M.op X0 (σ x)) (M.op X1 (σ x))) := by
          intro X0 X1
          first
          | (have i₁ := b7e23 X0 (σ x) (σ y) X1
             have i₂ := b7e510
             grind)
          | exact superpose b7e510 b7e23
          | exact resolve b7e23 b7e510
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e519 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op X1 (σ x))) = (M.op X0 (M.op X1 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b7e24 X1 (σ x) X0 (σ y)
             have i₂ := b7e510
             grind)
          | exact superpose b7e510 b7e24
          | exact resolve b7e24 b7e510
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e523 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (σ x)) := by
          first
          | (have i₁ := b7e121 (σ y) (σ x)
             have i₂ := b7e510
             grind)
          | exact superpose b7e510 b7e121
          | exact resolve b7e121 b7e510
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e525 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear b7e515
        have b7e526 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b7e519 X0 X1
             have i₂ := b7e11 X0 X1 (σ x)
             grind)
          | exact superpose b7e11 b7e519
          | exact resolve b7e519 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e519
        have b7e528 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 (σ y)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b7e517 X0 X1
             have i₂ := b7e11 X0 X1 (σ x)
             grind)
          | exact superpose b7e11 b7e517
          | exact resolve b7e517 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e517
        have b7e529 : (σ (k y x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b7e525
             have i₂ := b7e16 y x
             grind)
          | exact superpose b7e16 b7e525
          | exact resolve b7e525 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e525
        have b7e537 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b7e162 (τ X1) (τ X0)
             have i₂ := b7e43 X0 X1
             grind)
          | exact superpose b7e43 b7e162
          | exact resolve b7e162 b7e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e544 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b7e537 X0 X1
             have i₂ := b7e13 (k X0 X1)
             grind)
          | exact superpose b7e13 b7e537
          | (have j0 := b7e537 X0 X1
             grind)
          | exact resolve b7e537 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e537
        have b7e545 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b7e544 X0 X1
             have i₂ := b7e13 X1
             grind)
          | exact superpose b7e13 b7e544
          | (have j0 := b7e544 X0 X1
             grind)
          | exact resolve b7e544 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e544
        have b7e546 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e545 X0 X1
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e545
          | (have j0 := b7e545 X0 X1
             grind)
          | exact resolve b7e545 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e545
        have b7e547 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e546 X0 X1
             have i₂ := b7e13 (k X0 X1)
             grind)
          | exact superpose b7e13 b7e546
          | (have j0 := b7e546 X0 X1
             grind)
          | exact resolve b7e546 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e546
        have b7e704 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op X2 (M.op (σ y) X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e102 (σ y) X0 X2 X1
             have i₂ := b7e526 X0 X1
             grind)
          | exact superpose b7e526 b7e102
          | exact resolve b7e102 b7e526
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e714 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k (M.op X1 (σ y)) X0) = (M.op (M.op X1 (σ y)) (M.op X1 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b7e14 (M.op X1 (σ y)) X0
             have i₂ := b7e526 X0 X1
             grind)
          | exact superpose b7e526 b7e14
          | (have j0 := b7e14 X1 X0
             grind)
          | exact resolve b7e14 b7e526
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e744 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = (k (M.op X1 (σ y)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e714 X0 X1
             have i₂ := b7e11 X1 X1 (σ y)
             grind)
          | exact superpose b7e11 b7e714
          | (have j0 := b7e714 X0 X1
             grind)
          | (have r₁ := b7e714 (M.op X0 X1) (M.op X1 X1)
             have r₂ := b7e11 X0 X1 X1
             grind)
          | exact resolve b7e714 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e714
        have b7e1339 : (σ (k y x)) = (σ (k y y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b7e40 y y
             have i₂ := b7e529
             grind)
          | exact superpose b7e529 b7e40
          | exact resolve b7e40 b7e529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e1340 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (k y x)) X0) := by
          intro X0
          first
          | (have i₁ := b7e528 (σ y) X0
             have i₂ := b7e529
             grind)
          | exact superpose b7e529 b7e528
          | exact resolve b7e528 b7e529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e528
        have b7e1341 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (k y x))) := by
          intro X0
          first
          | (have i₁ := b7e526 X0 (σ y)
             have i₂ := b7e529
             grind)
          | exact superpose b7e529 b7e526
          | exact resolve b7e526 b7e529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e1347 : (σ y) ≠ (σ (k y x)) ∨ (σ (k y x)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b7e14 (σ y) (σ y)
             have i₂ := b7e529
             grind)
          | exact superpose b7e529 b7e14
          | exact resolve b7e14 b7e529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e1361 : (σ (k y x)) = (k (σ (k y x)) (σ (k y x))) := by
          first
          | (have i₁ := b7e121 (σ y) (σ y)
             have i₂ := b7e529
             grind)
          | exact superpose b7e529 b7e121
          | exact resolve b7e121 b7e529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e1363 : (σ (k y x)) = (σ (k (k y x) (k y x))) := by
          first
          | (have i₁ := b7e1361
             have i₂ := b7e16 (k y x) (k y x)
             grind)
          | exact superpose b7e16 b7e1361
          | exact resolve b7e1361 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1361
        have b7e1374 : (σ (k y x)) = (σ (k y y)) ∨ (σ y) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b7e1347
             have i₂ := b7e16 y y
             grind)
          | exact superpose b7e16 b7e1347
          | exact resolve b7e1347 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1347
        have b7e1385 : (σ (k y x)) = (σ (k y y)) := by
          first
          | (have r₁ := b7e1374
             have r₂ := b7e1339
             grind)
          | exact resolve b7e1374 b7e1339
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1339 b7e1374
        have b7e1660 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b7e1385
             have i₂ := b7e15 y x
             grind)
          | exact superpose b7e15 b7e1385
          | (have j1 := b7e15 y x
             grind)
          | exact resolve b7e1385 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e1664 : (k y x) = (τ (σ (k y y))) := by
          first
          | (have i₁ := b7e12 (k y x)
             have i₂ := b7e1385
             grind)
          | exact superpose b7e1385 b7e12
          | exact resolve b7e12 b7e1385
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e1693 : (k y x) = (k y y) := by
          first
          | (have i₁ := b7e1664
             have i₂ := b7e12 (k y y)
             grind)
          | exact superpose b7e12 b7e1664
          | exact resolve b7e1664 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1664
        have b7e1695 : (σ (M.op x y)) = (σ (k y y)) := by
          first
          | (have r₁ := b7e1660
             have r₂ := b7e20
             grind)
          | exact resolve b7e1660 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1660
        have b7e2117 : (M.op x y) = (k y y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b7e15 y x
             have i₂ := b7e1693
             grind)
          | exact superpose b7e1693 b7e15
          | (have j0 := b7e15 y x
             grind)
          | exact resolve b7e15 b7e1693
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e2118 : (M.op x y) = (k y y) := by
          first
          | (have r₁ := b7e2117
             have r₂ := b7e20
             grind)
          | exact resolve b7e2117 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2117
        have b7e2244 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b7e15 y y
             have i₂ := b7e2118
             grind)
          | exact superpose b7e2118 b7e15
          | (have j0 := b7e15 y y
             grind)
          | exact resolve b7e15 b7e2118
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e2256 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X2) = (M.op (σ (τ (k X0 X1))) (M.op X2 (σ (τ X0)))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e146 (τ X0) (τ X1) X2
             have i₂ := b7e43 X1 X0
             grind)
          | exact superpose b7e43 b7e146
          | (have j0 := b7e146 (τ X0) (τ X1) X2
             grind)
          | exact resolve b7e146 b7e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e43 b7e146
        have b7e2349 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X2) = (M.op (σ (τ (k X0 X1))) (M.op X2 X0)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e2256 X0 X1 X2
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e2256
          | (have j0 := b7e2256 X0 X1 X2
             grind)
          | exact resolve b7e2256 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2256
        have b7e2366 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X2) = (M.op (k X0 X1) (M.op X2 X0)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e2349 X0 X1 X2
             have i₂ := b7e13 (k X0 X1)
             grind)
          | exact superpose b7e13 b7e2349
          | (have j0 := b7e2349 X0 X1 X2
             grind)
          | exact resolve b7e2349 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2349
        have b7e2372 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (k X0 X1) (M.op X2 X0)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e2366 X0 X1 X2
             have i₂ := b7e13 X1
             grind)
          | exact superpose b7e13 b7e2366
          | (have j0 := b7e2366 X0 X1 X2
             grind)
          | exact resolve b7e2366 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2366
        have b7e2375 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X2) = (M.op (k X0 X1) (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e2372 X0 X1 X2
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e2372
          | (have j0 := b7e2372 X0 X1 X2
             grind)
          | exact resolve b7e2372 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2372
        have b7e2376 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (k X0 X1) (M.op X2 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e2375 X0 X0 X2
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e2375
          | (have j0 := b7e2375 X0 X1 X2
             grind)
          | exact resolve b7e2375 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2375
        have b7e3352 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (k y y)) X0) := by
          intro X0
          first
          | (have i₁ := b7e1340 X0
             have i₂ := b7e1385
             grind)
          | exact superpose b7e1385 b7e1340
          | exact resolve b7e1340 b7e1385
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1340
        have b7e3459 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x y)) X0) := by
          intro X0
          first
          | (have i₁ := b7e3352 X0
             have i₂ := b7e1695
             grind)
          | exact superpose b7e1695 b7e3352
          | exact resolve b7e3352 b7e1695
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e3352
        have b7e4312 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (k y y))) := by
          intro X0
          first
          | (have i₁ := b7e1341 X0
             have i₂ := b7e1385
             grind)
          | exact superpose b7e1385 b7e1341
          | exact resolve b7e1341 b7e1385
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1341 b7e1385
        have b7e4414 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
          intro X0
          first
          | (have i₁ := b7e4312 X0
             have i₂ := b7e1695
             grind)
          | exact superpose b7e1695 b7e4312
          | exact resolve b7e4312 b7e1695
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1695 b7e4312
        have b7e9147 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y y) (M.op X0 y)) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b7e11 x X0 y
             have i₂ := b7e2244
             grind)
          | exact superpose b7e2244 b7e11
          | exact resolve b7e11 b7e2244
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e9148 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 y) (M.op y y)) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b7e11 X0 x y
             have i₂ := b7e2244
             grind)
          | exact superpose b7e2244 b7e11
          | exact resolve b7e11 b7e2244
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2244
        have b7e9208 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b7e9148 X0
             have i₂ := b7e11 X0 y y
             grind)
          | exact superpose b7e11 b7e9148
          | exact resolve b7e9148 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e9148
        have b7e9209 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b7e9147 X0
             have i₂ := b7e11 y X0 y
             grind)
          | exact superpose b7e11 b7e9147
          | exact resolve b7e9147 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e9147
        have b7e10863 : ∀ X0 : G, y = (k y y) ∨ (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b7e121 y y
             have i₂ := b7e9208 X0
             grind)
          | exact superpose b7e9208 b7e121
          | (have j1 := b7e9208 X0
             grind)
          | exact resolve b7e121 b7e9208
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e121 b7e9208
        have b7e10867 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b7e10863 X0
             have i₂ := b7e2118
             grind)
          | exact superpose b7e2118 b7e10863
          | (have j0 := b7e10863 X0
             grind)
          | exact resolve b7e10863 b7e2118
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e10863
        have b7e13399 : (k (k y x) (k y x)) = (τ (σ (k y x))) := by
          first
          | (have i₁ := b7e12 (k (k y x) (k y x))
             have i₂ := b7e1363
             grind)
          | exact superpose b7e1363 b7e12
          | exact resolve b7e12 b7e1363
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1363
        have b7e13452 : (k y x) = (k (k y x) (k y x)) := by
          first
          | (have i₁ := b7e13399
             have i₂ := b7e12 (k y x)
             grind)
          | exact superpose b7e12 b7e13399
          | exact resolve b7e13399 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e13399
        have b7e13489 : (k y y) = (k (k y y) (k y y)) := by
          first
          | (have i₁ := b7e13452
             have i₂ := b7e1693
             grind)
          | exact superpose b7e1693 b7e13452
          | exact resolve b7e13452 b7e1693
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e13452
        have b7e13522 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
          first
          | (have i₁ := b7e13489
             have i₂ := b7e2118
             grind)
          | exact superpose b7e2118 b7e13489
          | exact resolve b7e13489 b7e2118
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e13489
        have b7e13664 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
          first
          | (have i₁ := b7e162 (M.op x y) (M.op x y)
             have i₂ := b7e13522
             grind)
          | exact superpose b7e13522 b7e162
          | exact resolve b7e162 b7e13522
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e13667 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
          first
          | (have i₁ := b7e547 (M.op x y) (M.op x y)
             have i₂ := b7e13522
             grind)
          | exact superpose b7e13522 b7e547
          | (have r₁ := b7e547 (M.op x y) (M.op x y)
             have r₂ := b7e13522
             grind)
          | exact resolve b7e547 b7e13522
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e547
        have b7e13668 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
        clear b7e13667
        have b7e13670 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
        clear b7e13664
        have b7e13674 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b7e13668
             have i₂ := b7e11 x x y
             grind)
          | exact superpose b7e11 b7e13668
          | exact resolve b7e13668 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e13668
        have b7e13677 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
          first
          | (have i₁ := b7e13670
             have i₂ := b7e4414 (σ (M.op x y))
             grind)
          | exact superpose b7e4414 b7e13670
          | exact resolve b7e13670 b7e4414
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e4414 b7e13670
        have b7e13690 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b7e13677
             have i₂ := b7e3459 (σ y)
             grind)
          | exact superpose b7e3459 b7e13677
          | exact resolve b7e13677 b7e3459
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e13677
        have b7e13781 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op x y))) := by
          intro X0 X1
          first
          | (have i₁ := b7e306 X0 X1 x
             have i₂ := b7e13674
             grind)
          | exact superpose b7e13674 b7e306
          | exact resolve b7e306 b7e13674
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e13784 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b7e11 x X0 x
             have i₂ := b7e13674
             grind)
          | exact superpose b7e13674 b7e11
          | exact resolve b7e11 b7e13674
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e13785 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b7e11 X0 x x
             have i₂ := b7e13674
             grind)
          | exact superpose b7e13674 b7e11
          | exact resolve b7e11 b7e13674
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e13787 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) (M.op X1 (M.op x X0))) := by
          intro X0 X1
          first
          | (have i₁ := b7e23 x x X0 X1
             have i₂ := b7e13674
             grind)
          | exact superpose b7e13674 b7e23
          | exact resolve b7e23 b7e13674
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e13790 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op X1 x)) = (M.op X0 (M.op X1 x)) := by
          intro X0 X1
          first
          | (have i₁ := b7e24 X1 x X0 x
             have i₂ := b7e13674
             grind)
          | exact superpose b7e13674 b7e24
          | exact resolve b7e24 b7e13674
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e13842 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op X1 x)) := by
          intro X0 X1
          first
          | (have i₁ := b7e13790 X0 X1
             have i₂ := b7e24 X1 x X0 y
             grind)
          | exact superpose b7e24 b7e13790
          | exact resolve b7e13790 b7e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e13790
        have b7e20944 : (τ (M.op (σ y) (σ y))) = (k (τ (M.op (σ y) (σ y))) x) := by
          first
          | (have i₁ := b7e28 (M.op (σ y) (σ y)) x
             have i₂ := b7e523
             grind)
          | exact superpose b7e523 b7e28
          | exact resolve b7e28 b7e523
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e28 b7e523
        have b7e20979 : (τ (σ (k y x))) = (k (τ (σ (k y x))) x) := by
          first
          | (have i₁ := b7e20944
             have i₂ := b7e529
             grind)
          | exact superpose b7e529 b7e20944
          | exact resolve b7e20944 b7e529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e529 b7e20944
        have b7e21002 : (k y x) = (k (k y x) x) := by
          first
          | (have i₁ := b7e20979
             have i₂ := b7e12 (k y x)
             grind)
          | exact superpose b7e12 b7e20979
          | exact resolve b7e20979 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e20979
        have b7e21024 : (k y y) = (k (k y y) x) := by
          first
          | (have i₁ := b7e21002
             have i₂ := b7e1693
             grind)
          | exact superpose b7e1693 b7e21002
          | exact resolve b7e21002 b7e1693
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1693 b7e21002
        have b7e21043 : (M.op x y) = (k (M.op x y) x) := by
          first
          | (have i₁ := b7e21024
             have i₂ := b7e2118
             grind)
          | exact superpose b7e2118 b7e21024
          | exact resolve b7e21024 b7e2118
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2118 b7e21024
        have b7e21269 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) := by
          first
          | (have i₁ := b7e15 (M.op x y) x
             have i₂ := b7e21043
             grind)
          | exact superpose b7e21043 b7e15
          | (have j0 := b7e15 (M.op x y) x
             grind)
          | exact resolve b7e15 b7e21043
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e27792 : (τ (M.op x y)) ≠ (τ (M.op x y)) ∨ (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
          first
          | (have i₁ := b7e424 (M.op x y) (M.op x y)
             have i₂ := b7e13522
             grind)
          | exact superpose b7e13522 b7e424
          | (have j0 := b7e424 (M.op x y) (M.op x y)
             grind)
          | exact resolve b7e424 b7e13522
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e424 b7e13522
        have b7e27831 : (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by grind
        clear b7e27792
        have b7e28093 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (τ (M.op x y)))) := by
          intro X0 X1
          first
          | (have i₁ := b7e306 X0 X1 (τ (M.op x y))
             have i₂ := b7e27831
             grind)
          | exact superpose b7e27831 b7e306
          | exact resolve b7e306 b7e27831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e27831
        have b7e29663 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (σ y)) (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b7e744 (M.op X0 x) (M.op x y)
             have i₂ := b7e13785 X0
             grind)
          | exact superpose b7e13785 b7e744
          | (have j0 := b7e744 (M.op X0 x) (M.op x y)
             grind)
          | (have r₁ := b7e744 (M.op X0 x) (M.op x y)
             have r₂ := b7e13785 X0
             grind)
          | exact resolve b7e744 b7e13785
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e744 b7e13785
        have b7e29692 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (σ y)) (M.op X0 x)) := by
          intro X0
          first
          | (have j0 := b7e29663 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e29663
        have b7e29704 : ∀ X0 : G, (M.op x x) = (k (M.op (M.op x y) (σ y)) (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b7e29692 X0
             have i₂ := b7e11 x x y
             grind)
          | exact superpose b7e11 b7e29692
          | exact resolve b7e29692 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e29692
        have b7e29741 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op x y) (σ y)) (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b7e29704 X0
             have i₂ := b7e13674
             grind)
          | exact superpose b7e13674 b7e29704
          | exact resolve b7e29704 b7e13674
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e29704
        have b7e30124 : (M.op x y) = (k (M.op (M.op x y) (σ y)) (M.op x y)) := by
          first
          | (have i₁ := b7e29741 x
             have i₂ := b7e13674
             grind)
          | exact superpose b7e13674 b7e29741
          | exact resolve b7e29741 b7e13674
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e13674 b7e29741
        have b7e30723 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) (σ y)))) := by
          first
          | (have i₁ := b7e157 (M.op x y) (M.op (M.op x y) (σ y))
             have i₂ := b7e30124
             grind)
          | exact superpose b7e30124 b7e157
          | (have j0 := b7e157 (M.op x y) (M.op (M.op x y) (σ y))
             grind)
          | exact resolve b7e157 b7e30124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e30725 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) (σ y))) (σ (M.op (M.op x y) (σ y)))) := by
          first
          | (have i₁ := b7e162 (M.op (M.op x y) (σ y)) (M.op x y)
             have i₂ := b7e30124
             grind)
          | exact superpose b7e30124 b7e162
          | exact resolve b7e162 b7e30124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e30124
        have b7e30738 : (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) (σ y))) (σ (M.op (M.op x y) (σ y)))) := by grind
        clear b7e30725
        have b7e30739 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) (σ y)))) := by grind
        clear b7e30723
        have b7e30747 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op (M.op x y) (σ y)))) := by
          first
          | (have i₁ := b7e30739
             have i₂ := b7e3459 (σ (M.op (M.op x y) (σ y)))
             grind)
          | exact superpose b7e3459 b7e30739
          | exact resolve b7e30739 b7e3459
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e30739
        have b7e31658 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
          intro X0
          first
          | (have j0 := b7e401 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e401
        have b7e32003 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X2 (σ (M.op X0 X0)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e306 X1 X2 (σ (M.op X0 X0))
             have i₂ := b7e31658 X0
             grind)
          | exact superpose b7e31658 b7e306
          | exact resolve b7e306 b7e31658
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e31658
        have b7e57672 : (σ (M.op x y)) = (σ (k (M.op (M.op x y) (σ y)) y)) ∨ (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b7e40 y (M.op (M.op x y) (σ y))
             have i₂ := b7e30747
             grind)
          | exact superpose b7e30747 b7e40
          | exact resolve b7e40 b7e30747
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e40
        have b7e57697 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ (M.op (M.op x y) (σ y))) (σ (M.op (M.op x y) (σ y)))) = (k (σ (M.op (M.op x y) (σ y))) (σ y)) := by
          first
          | (have i₁ := b7e14 (σ (M.op (M.op x y) (σ y))) (σ y)
             have i₂ := b7e30747
             grind)
          | exact superpose b7e30747 b7e14
          | (have j0 := b7e14 (σ (M.op (M.op x y) (σ y))) (σ y)
             grind)
          | exact resolve b7e14 b7e30747
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e30747
        have b7e57801 : (M.op (σ (M.op (M.op x y) (σ y))) (σ (M.op (M.op x y) (σ y)))) = (σ (k (M.op (M.op x y) (σ y)) y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b7e57697
             have i₂ := b7e16 (M.op (M.op x y) (σ y)) y
             grind)
          | exact superpose b7e16 b7e57697
          | exact resolve b7e57697 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e57697
        have b7e57868 : (σ (M.op x y)) = (σ (k (M.op (M.op x y) (σ y)) y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b7e57801
             have i₂ := b7e30738
             grind)
          | exact superpose b7e30738 b7e57801
          | exact resolve b7e57801 b7e30738
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e30738 b7e57801
        have b7e57910 : (σ (M.op x y)) = (σ (k (M.op (M.op x y) (σ y)) y)) := by
          first
          | (have r₁ := b7e57868
             have r₂ := b7e57672
             grind)
          | exact resolve b7e57868 b7e57672
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e57672 b7e57868
        have b7e58186 : (τ (σ (M.op x y))) = (k (M.op (M.op x y) (σ y)) y) := by
          first
          | (have i₁ := b7e12 (k (M.op (M.op x y) (σ y)) y)
             have i₂ := b7e57910
             grind)
          | exact superpose b7e57910 b7e12
          | exact resolve b7e12 b7e57910
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e57910
        have b7e58289 : (M.op x y) = (k (M.op (M.op x y) (σ y)) y) := by
          first
          | (have i₁ := b7e58186
             have i₂ := b7e12 (M.op x y)
             grind)
          | exact superpose b7e12 b7e58186
          | exact resolve b7e58186 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e58186
        have b7e58667 : (M.op x y) = (M.op y (M.op (M.op x y) (σ y))) ∨ y = (M.op y (M.op (M.op x y) (σ y))) := by
          first
          | (have i₁ := b7e15 (M.op (M.op x y) (σ y)) y
             have i₂ := b7e58289
             grind)
          | exact superpose b7e58289 b7e15
          | (have j0 := b7e15 (M.op (M.op x y) (σ y)) y
             grind)
          | exact resolve b7e15 b7e58289
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e58289
        have b7e58699 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op y (M.op (M.op x y) (σ y))) := by
          first
          | (have i₁ := b7e58667
             have i₂ := b7e526 y (M.op x y)
             grind)
          | exact superpose b7e526 b7e58667
          | exact resolve b7e58667 b7e526
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e58667
        have b7e58708 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) := by
          first
          | (have i₁ := b7e58699
             have i₂ := b7e526 y (M.op x y)
             grind)
          | exact superpose b7e526 b7e58699
          | exact resolve b7e58699 b7e526
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e526 b7e58699
        have b7e78598 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b7e2376 (M.op x y) x X0
             have i₂ := b7e21043
             grind)
          | exact superpose b7e21043 b7e2376
          | (have j0 := b7e2376 (M.op x y) x x
             grind)
          | exact resolve b7e2376 b7e21043
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2376 b7e21043
        have b7e79058 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) ∨ x = (M.op x (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b7e78598 X0
             have i₂ := b7e13787 y X0
             grind)
          | exact superpose b7e13787 b7e78598
          | exact resolve b7e78598 b7e13787
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e13787 b7e78598
        have b7e94329 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 x)) = (M.op x (M.op X0 y)) ∨ x = (M.op x (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b7e24 X0 x x y
             have i₂ := b7e21269
             grind)
          | exact superpose b7e21269 b7e24
          | exact resolve b7e24 b7e21269
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e21269
        have b7e94452 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 y)) ∨ x = (M.op x (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b7e94329 X0
             have i₂ := b7e13784 X0
             grind)
          | exact superpose b7e13784 b7e94329
          | exact resolve b7e94329 b7e13784
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e13784 b7e94329
        have b7e94638 : ∀ X0 X1 : G, (M.op x X0) = (M.op y X0) ∨ x = (M.op x y) ∨ (M.op X1 y) = (M.op X1 x) := by
          intro X0 X1
          first
          | (have i₁ := b7e79058 X0
             have i₂ := b7e10867 X0
             grind)
          | exact superpose b7e10867 b7e79058
          | (have j1 := b7e10867 X1
             grind)
          | exact resolve b7e79058 b7e10867
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e10867 b7e79058
        have b7e95103 : ∀ X0 X1 : G, (M.op x X0) = (M.op y X0) ∨ (M.op X1 y) = (M.op X1 x) := by
          intro X0 X1
          first
          | (have j0 := b7e94638 X0 X1
             grind)
          | (have r₁ := b7e94638 X0 X1
             have r₂ := b7e20
             grind)
          | exact resolve b7e94638 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e94638
        have b7e95657 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y (τ (M.op x y)))) ∨ (M.op X1 y) = (M.op X1 x) := by
          intro X0 X1
          first
          | (have i₁ := b7e28093 X0 x
             have i₂ := b7e95103 (τ (M.op x y)) X1
             grind)
          | exact superpose b7e95103 b7e28093
          | (have j1 := b7e95103 X0 X1
             grind)
          | exact resolve b7e28093 b7e95103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e95103
        have b7e95947 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op X1 y) = (M.op X1 x) := by
          intro X0 X1
          first
          | (have i₁ := b7e95657 X0 X1
             have i₂ := b7e28093 X0 y
             grind)
          | exact superpose b7e28093 b7e95657
          | (have j0 := b7e95657 X0 X0
             grind)
          | exact resolve b7e95657 b7e28093
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e28093 b7e95657
        have b7e99891 : ∀ X0 : G, (M.op X0 y) ≠ (M.op X0 y) ∨ (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have j0 := b7e95947 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e95947
        have b7e99892 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have j0 := b7e99891 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e99891
        have b7e100635 : ∀ X0 : G, (M.op X0 y) ≠ X0 ∨ (M.op x x) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b7e14 x X0
             have i₂ := b7e99892 X0
             grind)
          | exact superpose b7e99892 b7e14
          | (have j0 := b7e14 y X0
             grind)
          | exact resolve b7e14 b7e99892
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e100746 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) y) = (M.op X0 (M.op x (M.op X2 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e102 X2 X0 x X1
             have i₂ := b7e99892 (M.op X0 (M.op X1 X2))
             grind)
          | exact superpose b7e99892 b7e102
          | exact resolve b7e102 b7e99892
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e100797 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b7e18
             have i₂ := b7e99892 y
             grind)
          | exact superpose b7e99892 b7e18
          | exact resolve b7e18 b7e99892
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e100833 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x (M.op X2 X1))) = (M.op X0 (M.op y (M.op X2 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e100746 X0 X1 X2
             have i₂ := b7e102 X2 X0 y X1
             grind)
          | exact superpose b7e102 b7e100746
          | exact resolve b7e100746 b7e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e100746
        have b7e100921 : ∀ X0 : G, (M.op X0 y) ≠ X0 ∨ (M.op x y) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b7e100635 X0
             have i₂ := b7e99892 x
             grind)
          | exact superpose b7e99892 b7e100635
          | (have j0 := b7e100635 X0
             grind)
          | exact resolve b7e100635 b7e99892
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e99892 b7e100635
        have b7e108724 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op y (M.op X1 X2))) = (M.op X0 (M.op x X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e24 x (M.op X1 X2) X0 X3
             have i₂ := b7e100833 (M.op X0 (M.op (M.op X1 X2) X3)) X2 X1
             grind)
          | exact superpose b7e100833 b7e24
          | exact resolve b7e24 b7e100833
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e100833
        have b7e108833 : ∀ X0 X3 : G, (M.op X0 (M.op y X3)) = (M.op X0 (M.op x X3)) := by
          intro X0 X3
          first
          | (have i₁ := b7e108724 X0 x x X3
             have i₂ := b7e24 y (M.op x x) X0 X3
             grind)
          | exact superpose b7e24 b7e108724
          | exact resolve b7e108724 b7e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e108724
        have b7e110249 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op y X0)) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b7e9209 (M.op x X0)
             have i₂ := b7e108833 x X0
             grind)
          | exact superpose b7e108833 b7e9209
          | exact resolve b7e9209 b7e108833
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e9209
        have b7e110256 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have j0 := b7e110249 X0
             grind)
          | (have r₁ := b7e110249 X0
             have r₂ := b7e100797
             grind)
          | exact resolve b7e110249 b7e100797
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e100797 b7e110249
        have b7e110622 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b7e110256 X0
             have i₂ := b7e108833 y X0
             grind)
          | exact superpose b7e108833 b7e110256
          | exact resolve b7e110256 b7e108833
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e110256
        have b7e111685 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op y (M.op y X0)) (M.op X1 (M.op y X0))) := by
          intro X0 X1
          first
          | (have i₁ := b7e11 x X1 (M.op y X0)
             have i₂ := b7e110622 X0
             grind)
          | exact superpose b7e110622 b7e11
          | exact resolve b7e11 b7e110622
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e111787 : ∀ X1 : G, (M.op x X1) = (M.op y X1) := by
          intro X1
          first
          | (have i₁ := b7e111685 x X1
             have i₂ := b7e11 y X1 (M.op y x)
             grind)
          | exact superpose b7e11 b7e111685
          | exact resolve b7e111685 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e111685
        have b7e112356 : x ≠ (M.op y y) := by
          first
          | (have i₁ := b7e20
             have i₂ := b7e111787 y
             grind)
          | exact superpose b7e111787 b7e20
          | exact resolve b7e20 b7e111787
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e112359 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op y y)) X0) := by
          intro X0
          first
          | (have i₁ := b7e3459 X0
             have i₂ := b7e111787 y
             grind)
          | exact superpose b7e111787 b7e3459
          | exact resolve b7e3459 b7e111787
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e3459
        have b7e139889 : ∀ X0 : G, x = (M.op x (M.op y y)) ∨ (M.op x X0) = (M.op x (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b7e108833 x y
             have i₂ := b7e94452 X0
             grind)
          | exact superpose b7e94452 b7e108833
          | (have j1 := b7e94452 X0
             grind)
          | exact resolve b7e108833 b7e94452
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e94452
        have b7e139983 : ∀ X0 : G, x = (M.op y (M.op y y)) ∨ (M.op x X0) = (M.op x (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b7e139889 X0
             have i₂ := b7e110622 y
             grind)
          | exact superpose b7e110622 b7e139889
          | (have j0 := b7e139889 X0
             grind)
          | exact resolve b7e139889 b7e110622
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e110622 b7e139889
        have b7e140123 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 y)) ∨ x = (M.op y (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b7e139983 X0
             have i₂ := b7e111787 (M.op X0 y)
             grind)
          | exact superpose b7e111787 b7e139983
          | exact resolve b7e139983 b7e111787
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e139983
        have b7e140230 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 y)) ∨ x = (M.op y (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b7e140123 X0
             have i₂ := b7e111787 X0
             grind)
          | exact superpose b7e111787 b7e140123
          | exact resolve b7e140123 b7e111787
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e140123
        have b7e219488 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op x y))) = (M.op (M.op X0 (M.op x y)) (M.op X1 y)) ∨ y = (M.op y (M.op x y)) := by
          intro X0 X1
          first
          | (have i₁ := b7e24 X1 y X0 (M.op x y)
             have i₂ := b7e58708
             grind)
          | exact superpose b7e58708 b7e24
          | exact resolve b7e24 b7e58708
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e24 b7e58708
        have b7e219503 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op x y))) = (M.op X0 (M.op (M.op X1 y) (M.op y x))) ∨ y = (M.op y (M.op x y)) := by
          intro X0 X1
          first
          | (have i₁ := b7e219488 X0 X1
             have i₂ := b7e102 y X0 (M.op X1 y) x
             grind)
          | exact superpose b7e102 b7e219488
          | exact resolve b7e219488 b7e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e102 b7e219488
        have b7e219529 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op x y))) = (M.op X0 (M.op (M.op X1 y) (M.op y y))) ∨ y = (M.op y (M.op x y)) := by
          intro X0 X1
          first
          | (have i₁ := b7e219503 X0 X1
             have i₂ := b7e13842 (M.op X1 y) y
             grind)
          | exact superpose b7e13842 b7e219503
          | exact resolve b7e219503 b7e13842
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e13842 b7e219503
        have b7e219548 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op X1 (M.op x y))) ∨ y = (M.op y (M.op x y)) := by
          intro X0 X1
          first
          | (have i₁ := b7e219529 X0 X1
             have i₂ := b7e306 X0 (M.op X1 y) y
             grind)
          | exact superpose b7e306 b7e219529
          | exact resolve b7e219529 b7e306
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e306 b7e219529
        have b7e219563 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 y)) ∨ y = (M.op y (M.op x y)) := by
          intro X0 X1
          first
          | (have i₁ := b7e219548 X0 X1
             have i₂ := b7e13781 X0 X1
             grind)
          | exact superpose b7e13781 b7e219548
          | exact resolve b7e219548 b7e13781
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e13781 b7e219548
        have b7e219573 : ∀ X0 X1 : G, y = (M.op y (M.op y y)) ∨ (M.op X0 X1) = (M.op X0 (M.op X1 y)) := by
          intro X0 X1
          first
          | (have i₁ := b7e219563 X0 X1
             have i₂ := b7e108833 y y
             grind)
          | exact superpose b7e108833 b7e219563
          | (have j0 := b7e219563 X0 X1
             grind)
          | exact resolve b7e219563 b7e108833
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e108833 b7e219563
        have b7e235625 : ∀ X0 : G, x = (M.op y y) ∨ x = y ∨ (M.op y X0) = (M.op y (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b7e219573 y y
             have i₂ := b7e140230 X0
             grind)
          | exact superpose b7e140230 b7e219573
          | (have j0 := b7e219573 y X0
             have j1 := b7e140230 X0
             grind)
          | exact resolve b7e219573 b7e140230
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e140230 b7e219573
        have b7e235673 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 y)) ∨ x = y := by
          intro X0
          first
          | (have j0 := b7e235625 X0
             grind)
          | (have r₁ := b7e235625 X0
             have r₂ := b7e112356
             grind)
          | exact resolve b7e235625 b7e112356
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e112356 b7e235625
        have b7e236661 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op y X0) (M.op X1 (M.op X0 y))) ∨ x = y := by
          intro X0 X1
          first
          | (have i₁ := b7e11 y X1 (M.op X0 y)
             have i₂ := b7e235673 X0
             grind)
          | exact superpose b7e235673 b7e11
          | exact resolve b7e11 b7e235673
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e235673
        have b7e236714 : ∀ X1 : G, (M.op y X1) = (M.op (M.op y y) X1) ∨ x = y := by
          intro X1
          first
          | (have i₁ := b7e236661 x X1
             have i₂ := b7e23 y x y X1
             grind)
          | exact superpose b7e23 b7e236661
          | exact resolve b7e236661 b7e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e23 b7e236661
        have b7e238822 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (k x (M.op y y)) ∨ x = y := by
          first
          | (have i₁ := b7e100921 (M.op y y)
             have i₂ := b7e236714 y
             grind)
          | exact superpose b7e236714 b7e100921
          | (have j0 := b7e100921 (M.op y y)
             grind)
          | (have r₁ := b7e100921 (M.op y y)
             have r₂ := b7e236714 y
             grind)
          | exact resolve b7e100921 b7e236714
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e100921 b7e236714
        have b7e238832 : (M.op x y) = (k x (M.op y y)) ∨ x = y := by grind
        clear b7e238822
        have b7e238837 : (M.op y y) = (k x (M.op y y)) ∨ x = y := by
          first
          | (have i₁ := b7e238832
             have i₂ := b7e111787 y
             grind)
          | exact superpose b7e111787 b7e238832
          | exact resolve b7e238832 b7e111787
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e111787 b7e238832
        have b7e241827 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b7e157 (M.op y y) x
             have i₂ := b7e238837
             grind)
          | exact superpose b7e238837 b7e157
          | (have j0 := b7e157 (M.op y y) x
             grind)
          | exact resolve b7e157 b7e238837
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e157
        have b7e241828 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ x = y := by
          first
          | (have i₁ := b7e162 x (M.op y y)
             have i₂ := b7e238837
             grind)
          | exact superpose b7e238837 b7e162
          | exact resolve b7e162 b7e238837
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e162 b7e238837
        have b7e241838 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ x = y := by grind
        clear b7e241828
        have b7e241839 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ x)) ∨ x = y := by grind
        clear b7e241827
        have b7e241847 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ x = y := by
          first
          | (have i₁ := b7e241839
             have i₂ := b7e112359 (σ x)
             grind)
          | exact superpose b7e112359 b7e241839
          | exact resolve b7e241839 b7e112359
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e241839
        have b7e245223 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op X0 (M.op X1 (σ (M.op y y)))) ∨ x = y := by
          intro X0 X1
          first
          | (have i₁ := b7e704 X0 (σ x) X1
             have i₂ := b7e241847
             grind)
          | exact superpose b7e241847 b7e704
          | exact resolve b7e704 b7e241847
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e704 b7e241847
        have b7e245263 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 (σ x)) X1) ∨ x = y := by
          intro X0 X1
          first
          | (have i₁ := b7e245223 X0 X1
             have i₂ := b7e32003 y X0 X1
             grind)
          | exact superpose b7e32003 b7e245223
          | exact resolve b7e245223 b7e32003
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e32003 b7e245223
        have b7e246692 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y y)) X0) ∨ x = y ∨ x = y := by
          intro X0
          first
          | (have i₁ := b7e245263 (σ x) X0
             have i₂ := b7e241838
             grind)
          | exact superpose b7e241838 b7e245263
          | exact resolve b7e245263 b7e241838
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e241838 b7e245263
        have b7e247117 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y y)) X0) ∨ x = y := by
          intro X0
          first
          | (have j0 := b7e246692 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e246692
        have b7e247367 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b7e247117 X0
             have i₂ := b7e112359 X0
             grind)
          | exact superpose b7e112359 b7e247117
          | exact resolve b7e247117 b7e112359
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e112359 b7e247117
        have b7e247890 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e247367 (σ y)
             grind)
          | exact superpose b7e247367 b7e17
          | exact resolve b7e17 b7e247367
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e247367
        have b7e248365 : x = y := by
          first
          | (have r₁ := b7e247890
             have r₂ := b7e13690
             grind)
          | exact resolve b7e247890 b7e13690
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e13690 b7e247890
        have b7e248783 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b7e19
             have i₂ := b7e248365
             grind)
          | exact superpose b7e248365 b7e19
          | exact resolve b7e19 b7e248365
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e248786 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b7e510
             have i₂ := b7e248365
             grind)
          | exact superpose b7e248365 b7e510
          | exact resolve b7e510 b7e248365
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e510 b7e248365
        have b7e248946 : False := by grind
        exact b7e248946

/-- `Equation4385`: `x ◇ (x ◇ x) = (y ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4385 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4385 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4385.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op (M.op x y) (M.op x y)) (x) with h2a | h2a
      · have b0e11 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X0) := by
          intro X0 X1
          grind
        have b0e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e18 : y = (M.op x x) := by grind
        have b0e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b0e20 : x = (M.op (M.op x y) (M.op x y)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b0e34 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = (M.op (M.op x y) x) := by
          intro X0
          first
          | (have i₁ := b0e11 (M.op x y) X0
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e11
          | exact resolve b0e11 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e36 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X1) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e11 X1 X2
             have i₂ := b0e11 X1 X0
             grind)
          | exact superpose b0e11 b0e11
          | exact resolve b0e11 b0e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e37 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
          first
          | (have i₁ := b0e11 (M.op x y) (M.op x y)
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e11
          | exact resolve b0e11 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e40 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b0e11 x x
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e11
          | exact resolve b0e11 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e41 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = (M.op x (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b0e34 X0
             have i₂ := b0e37
             grind)
          | exact superpose b0e37 b0e34
          | exact resolve b0e34 b0e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e34
        have b0e42 : (M.op (M.op x y) x) = (M.op x (M.op x x)) := by
          first
          | (have i₁ := b0e11 x y
             have i₂ := b0e40
             grind)
          | exact superpose b0e40 b0e11
          | exact resolve b0e11 b0e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e40
        have b0e43 : (M.op x y) = (M.op (M.op x y) x) := by
          first
          | (have i₁ := b0e42
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e42
          | exact resolve b0e42 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e42
        have b0e137 : (M.op x y) = (M.op x (M.op x y)) := by
          first
          | (have i₁ := b0e43
             have i₂ := b0e37
             grind)
          | exact superpose b0e37 b0e43
          | exact resolve b0e43 b0e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e37 b0e43
        have b0e150 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b0e36 x (M.op x y) X0
             have i₂ := b0e137
             grind)
          | exact superpose b0e137 b0e36
          | exact resolve b0e36 b0e137
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e36
        have b0e151 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) := by
          first
          | (have i₁ := b0e150 x
             have i₂ := b0e41 x
             grind)
          | exact superpose b0e41 b0e150
          | exact resolve b0e150 b0e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41 b0e150
        have b0e153 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
          first
          | (have i₁ := b0e151
             have i₂ := b0e137
             grind)
          | exact superpose b0e137 b0e151
          | exact resolve b0e151 b0e137
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e137 b0e151
        have b0e155 : x = (M.op x y) := by
          first
          | (have i₁ := b0e153
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e153
          | exact resolve b0e153 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e153
        have b0e166 : x = (M.op x x) := by
          first
          | (have i₁ := b0e20
             have i₂ := b0e155
             grind)
          | exact superpose b0e155 b0e20
          | exact resolve b0e20 b0e155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e155
        have b0e214 : x = y := by
          first
          | (have i₁ := b0e18
             have i₂ := b0e166
             grind)
          | exact superpose b0e166 b0e18
          | exact resolve b0e18 b0e166
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e166
        have b0e242 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e214
             grind)
          | exact superpose b0e214 b0e17
          | exact resolve b0e17 b0e214
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e214
        have b0e254 : (σ y) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e242
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e242
          | exact resolve b0e242 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e242
        have b0e259 : False := by grind
        exact b0e259
      · have b1e11 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X0) := by
          intro X0 X1
          grind
        have b1e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e18 : y = (M.op x x) := by grind
        have b1e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b1e20 : x ≠ (M.op (M.op x y) (M.op x y)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b1e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 (τ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e16
          | exact resolve b1e16 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X1 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e16
          | exact resolve b1e16 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e11 (σ x) X0
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e11
          | exact resolve b1e11 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b1e11 x x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e11
          | exact resolve b1e11 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : (M.op x (M.op x x)) = (M.op (M.op x y) x) := by
          first
          | (have i₁ := b1e11 x y
             have i₂ := b1e31
             grind)
          | exact superpose b1e31 b1e11
          | exact resolve b1e11 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e33 : (M.op x y) = (M.op (M.op x y) x) := by
          first
          | (have i₁ := b1e32
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e32
          | exact resolve b1e32 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e38 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X1) X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e11 X1 X2
             have i₂ := b1e15 X1 X0
             grind)
          | (have i₁ := b1e11 X0 X1
             have i₂ := b1e15 X0 (M.op X0 X0)
             grind)
          | exact superpose b1e15 b1e11
          | (have j1 := b1e15 X1 X0
             grind)
          | exact resolve b1e11 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X0 X1
             have i₂ := b1e15 (σ X0) (σ X1)
             grind)
          | exact superpose b1e15 b1e16
          | (have j1 := b1e15 (σ X0) (σ X1)
             grind)
          | exact resolve b1e16 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (k (τ X0) X1)
             have i₂ := b1e25 X0 X1
             grind)
          | exact superpose b1e25 b1e12
          | exact resolve b1e12 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e105 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e52 X1 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e52
          | exact resolve b1e52 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e143 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e39 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e194 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
          first
          | (have i₁ := b1e143 (M.op x y) x
             have i₂ := b1e33
             grind)
          | exact superpose b1e33 b1e143
          | (have j0 := b1e143 (M.op x y) x
             grind)
          | (have r₁ := b1e143 (M.op x y) x
             have r₂ := b1e33
             grind)
          | exact resolve b1e143 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e143
        have b1e200 : (M.op x y) = (k (M.op x y) x) := by grind
        clear b1e194
        have b1e323 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 X0 x
             have i₂ := b1e38 X1 X0 x
             grind)
          | exact superpose b1e38 b1e11
          | (have j1 := b1e38 X1 X0 x
             grind)
          | exact resolve b1e11 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e395 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e44 X0 X0
             have i₂ := b1e15 (σ X0) X1
             grind)
          | (have i₁ := b1e44 X0 X1
             have i₂ := b1e15 X0 (M.op (σ X0) (σ X1))
             grind)
          | exact superpose b1e15 b1e44
          | (have j1 := b1e15 (σ X1) X0
             grind)
          | exact resolve b1e44 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e423 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1
             have i₂ := b1e44 X0 X1
             grind)
          | exact superpose b1e44 b1e12
          | (have j1 := b1e44 X0 X1
             grind)
          | exact resolve b1e12 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e425 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e16 X1 X2
             have i₂ := b1e44 X0 X2
             grind)
          | exact superpose b1e44 b1e16
          | (have j1 := b1e44 X0 X2
             grind)
          | exact resolve b1e16 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e3077 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e423 (τ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e423
          | exact resolve b1e423 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e423
        have b1e3159 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e3077 X0 X1
             have i₂ := b1e25 X0 X1
             grind)
          | exact superpose b1e25 b1e3077
          | (have j0 := b1e3077 X0 X1
             grind)
          | exact resolve b1e3077 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3077
        have b1e4147 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e395 X0 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e395
          | (have j0 := b1e395 X1 (τ X0)
             grind)
          | exact resolve b1e395 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e395
        have b1e4264 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e4147 X0 X1
             have i₂ := b1e26 X0 (τ X0)
             grind)
          | exact superpose b1e26 b1e4147
          | (have j0 := b1e4147 X0 X1
             grind)
          | exact resolve b1e4147 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e4147
        have b1e4277 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e4264 X0 X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e4264
          | (have j0 := b1e4264 X0 X1
             grind)
          | exact resolve b1e4264 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4264
        have b1e12607 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e425 (τ X0) X1 X2
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e425
          | exact resolve b1e425 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e425
        have b1e12844 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12607 X0 X1 X2
             have i₂ := b1e25 X0 X1
             grind)
          | exact superpose b1e25 b1e12607
          | (have j0 := b1e12607 X0 X1 X2
             grind)
          | exact resolve b1e12607 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e12607
        have b1e27220 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e3159 X0 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e3159
          | (have j0 := b1e3159 X1 (τ X0)
             grind)
          | exact resolve b1e3159 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3159
        have b1e49098 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) (M.op X2 X2)) ∨ (M.op X2 (σ (τ X1))) = (k X2 (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12844 X2 (τ X1) (τ X0)
             have i₂ := b1e105 X1 X0
             grind)
          | exact superpose b1e105 b1e12844
          | (have j0 := b1e12844 X2 (τ X1) X2
             grind)
          | exact resolve b1e12844 b1e105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e105 b1e12844
        have b1e49123 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 (M.op X2 X2)) ∨ (M.op X2 (σ (τ X1))) = (k X2 (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e49098 X0 X1 X2
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e49098
          | (have j0 := b1e49098 X0 X1 X2
             grind)
          | exact resolve b1e49098 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49098
        have b1e49126 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (M.op X2 (σ (τ X1))) = (k X2 (σ (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e49123 X0 X1 X2
             have i₂ := b1e13 (k X0 X1)
             grind)
          | exact superpose b1e13 b1e49123
          | (have j0 := b1e49123 X0 X1 X2
             grind)
          | exact resolve b1e49123 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49123
        have b1e49127 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 X1) ∨ (k X0 X1) = (k X0 (M.op X2 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e49126 X0 X0 X2
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e49126
          | (have j0 := b1e49126 X0 X1 X2
             grind)
          | exact resolve b1e49126 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49126
        have b1e56001 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 (M.op X0 X0)) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b1e49127 X0 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49127
        have b1e56002 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        clear b1e56001
        have b1e56090 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e56002 X0 X0
             have i₂ := b1e15 X0 X1
             grind)
          | (have i₁ := b1e56002 X0 X1
             have i₂ := b1e15 X0 (M.op X0 X1)
             grind)
          | exact superpose b1e15 b1e56002
          | (have j0 := b1e56002 X1 X0
             have j1 := b1e15 X1 X0
             grind)
          | (have r₁ := b1e56002 X1 X1
             have r₂ := b1e15 X1 X1
             grind)
          | (have r₁ := b1e56002 (M.op X0 X0) X1
             have r₂ := b1e15 X0 (M.op (M.op X0 X0) X1)
             grind)
          | exact resolve b1e56002 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e56192 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e56090 X0 X1
             have j1 := b1e4277 X1 X0
             grind)
          | (have r₁ := b1e56090 (k X0 X1) (M.op X0 X1)
             have r₂ := b1e4277 X0 X1
             grind)
          | (have r₁ := b1e56090 (M.op X0 X1) (k X0 X1)
             have r₂ := b1e4277 X0 X1
             grind)
          | (have r₁ := b1e56090 (k X0 X0) X1
             have r₂ := b1e4277 X0 X1
             grind)
          | exact resolve b1e56090 b1e4277
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4277 b1e56090
        have b1e56551 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          grind
        clear b1e56192
        have b1e59087 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e323 X0 X1
             have i₂ := b1e56551 X0
             grind)
          | exact superpose b1e56551 b1e323
          | (have j0 := b1e323 X0 X1
             have j1 := b1e56551 X0
             grind)
          | exact resolve b1e323 b1e56551
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e323 b1e56551
        have b1e59120 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e59087 X0 X1
             have j1 := b1e56002 X0 X1
             grind)
          | (have r₁ := b1e59087 X0 X1
             have r₂ := b1e56002 X0 X1
             grind)
          | exact resolve b1e59087 b1e56002
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56002 b1e59087
        have b1e60560 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e59120 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59120
        have b1e60561 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e60560 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60560
        have b1e60784 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 X0
             have i₂ := b1e60561 (σ X0)
             grind)
          | exact superpose b1e60561 b1e16
          | exact resolve b1e16 b1e60561
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e60936 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e60784 X0
             have i₂ := b1e60561 X0
             grind)
          | exact superpose b1e60561 b1e60784
          | exact resolve b1e60784 b1e60561
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60561 b1e60784
        have b1e61570 : ∀ X0 X1 : G, (τ X1) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e27220 X1 (σ X0)
             have i₂ := b1e60936 X0
             grind)
          | exact superpose b1e60936 b1e27220
          | (have j0 := b1e27220 X1 (σ X0)
             grind)
          | exact resolve b1e27220 b1e60936
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27220 b1e60936
        have b1e61626 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e61570 X0 X1
             have i₂ := b1e12 (M.op X0 X0)
             grind)
          | exact superpose b1e12 b1e61570
          | (have j0 := b1e61570 X0 X1
             grind)
          | exact resolve b1e61570 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61570
        have b1e66344 : ∀ X0 : G, (τ X0) ≠ x ∨ (k (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X0) := by
          intro X0
          first
          | (have i₁ := b1e20
             have i₂ := b1e61626 (M.op x y) X0
             grind)
          | exact superpose b1e61626 b1e20
          | (have j1 := b1e61626 (M.op x y) X0
             grind)
          | exact resolve b1e20 b1e61626
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61626
        have b1e104719 : ∀ X0 : G, x ≠ X0 ∨ (k (σ (M.op x y)) (σ X0)) = (M.op (σ (M.op x y)) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e66344 (σ X0)
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e66344
          | (have j0 := b1e66344 (σ X0)
             grind)
          | (have r₁ := b1e66344 (σ x)
             have r₂ := b1e12 x
             grind)
          | exact resolve b1e66344 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66344
        have b1e104720 : ∀ X0 : G, x ≠ X0 ∨ (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e104719 X0
             have i₂ := b1e16 (M.op x y) X0
             grind)
          | exact superpose b1e16 b1e104719
          | (have j0 := b1e104719 X0
             grind)
          | exact resolve b1e104719 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e104719
        have b1e105376 : (σ (k (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) := by
          first
          | (have j0 := b1e104720 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e104720
        have b1e105377 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
          first
          | (have i₁ := b1e105376
             have i₂ := b1e200
             grind)
          | exact superpose b1e200 b1e105376
          | exact resolve b1e105376 b1e200
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e200 b1e105376
        have b1e105387 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) := by
          first
          | (have i₁ := b1e27 (σ (M.op x y))
             have i₂ := b1e105377
             grind)
          | exact superpose b1e105377 b1e27
          | exact resolve b1e27 b1e105377
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e105408 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e105387
             have i₂ := b1e105377
             grind)
          | exact superpose b1e105377 b1e105387
          | exact resolve b1e105387 b1e105377
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e105377 b1e105387
        have b1e105422 : False := by grind
        exact b1e105422
    · rcases eq_or_ne (M.op (M.op x y) (M.op x y)) (x) with h2a | h2a
      · have b2e11 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X0) := by
          intro X0 X1
          grind
        have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e18 : y = (M.op x x) := by grind
        have b2e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e20 : x = (M.op (M.op x y) (M.op x y)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b2e22 : x = (k x y) := by grind
        have b2e32 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = (M.op (M.op x y) x) := by
          intro X0
          first
          | (have i₁ := b2e11 (M.op x y) X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e11
          | exact resolve b2e11 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X1) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e11 X1 X2
             have i₂ := b2e11 X1 X0
             grind)
          | exact superpose b2e11 b2e11
          | exact resolve b2e11 b2e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b2e11 x x
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e11
          | exact resolve b2e11 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
          first
          | (have i₁ := b2e11 (M.op x y) (M.op x y)
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e11
          | exact resolve b2e11 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
          intro X0
          first
          | (have i₁ := b2e11 X0 (M.op x X0)
             have i₂ := b2e11 X0 x
             grind)
          | exact superpose b2e11 b2e11
          | exact resolve b2e11 b2e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e37 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = (M.op x (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b2e32 X0
             have i₂ := b2e35
             grind)
          | exact superpose b2e35 b2e32
          | exact resolve b2e32 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e48 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e19
             have i₂ := b2e15 (σ x) X0
             grind)
          | (have i₁ := b2e19
             have i₂ := b2e15 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b2e15 b2e19
          | (have j1 := b2e15 (σ x) X0
             grind)
          | (have r₁ := b2e19
             have r₂ := b2e15 (σ x) (σ y)
             grind)
          | exact resolve b2e19 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e92 : ∀ X0 : G, (M.op (M.op X0 x) x) = (M.op (M.op x y) x) := by
          intro X0
          first
          | (have i₁ := b2e33 X0 x y
             have i₂ := b2e34
             grind)
          | exact superpose b2e34 b2e33
          | exact resolve b2e33 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e100 : ∀ X0 : G, (M.op (M.op X0 x) x) = (M.op x (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b2e92 X0
             have i₂ := b2e35
             grind)
          | exact superpose b2e35 b2e92
          | exact resolve b2e92 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35 b2e92
        have b2e106 : (M.op x (M.op x x)) = (M.op x (M.op x y)) := by
          first
          | (have i₁ := b2e100 x
             have i₂ := b2e11 x x
             grind)
          | exact superpose b2e11 b2e100
          | exact resolve b2e100 b2e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e100
        have b2e112 : (M.op x y) = (M.op x (M.op x y)) := by
          first
          | (have i₁ := b2e106
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e106
          | exact resolve b2e106 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e106
        have b2e117 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b2e33 x (M.op x y) X0
             have i₂ := b2e112
             grind)
          | exact superpose b2e112 b2e33
          | exact resolve b2e33 b2e112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e118 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) := by
          first
          | (have i₁ := b2e117 x
             have i₂ := b2e37 x
             grind)
          | exact superpose b2e37 b2e117
          | exact resolve b2e117 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37 b2e117
        have b2e120 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
          first
          | (have i₁ := b2e118
             have i₂ := b2e112
             grind)
          | exact superpose b2e112 b2e118
          | exact resolve b2e118 b2e112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e112 b2e118
        have b2e122 : x = (M.op x y) := by
          first
          | (have i₁ := b2e120
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e120
          | exact resolve b2e120 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e120
        have b2e168 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
          first
          | (have i₁ := b2e36 (M.op x y)
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e36
          | exact resolve b2e36 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36
        have b2e174 : (M.op x x) = (M.op (M.op x x) x) := by
          first
          | (have i₁ := b2e168
             have i₂ := b2e122
             grind)
          | exact superpose b2e122 b2e168
          | exact resolve b2e168 b2e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e168
        have b2e175 : (M.op x x) = (M.op x (M.op x x)) := by
          first
          | (have i₁ := b2e174
             have i₂ := b2e11 x x
             grind)
          | exact superpose b2e11 b2e174
          | exact resolve b2e174 b2e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e174
        have b2e176 : y = (M.op x y) := by
          first
          | (have i₁ := b2e175
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e175
          | exact resolve b2e175 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e175
        have b2e177 : x = y := by
          first
          | (have i₁ := b2e176
             have i₂ := b2e122
             grind)
          | exact superpose b2e122 b2e176
          | exact resolve b2e176 b2e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e122 b2e176
        have b2e197 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e48 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e198 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e197
             have i₂ := b2e16 x y
             grind)
          | exact superpose b2e16 b2e197
          | exact resolve b2e197 b2e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e197
        have b2e199 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e198
             have i₂ := b2e22
             grind)
          | exact superpose b2e22 b2e198
          | exact resolve b2e198 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22 b2e198
        have b2e200 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e199
             have i₂ := b2e177
             grind)
          | exact superpose b2e177 b2e199
          | exact resolve b2e199 b2e177
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e199
        have b2e251 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e200
             grind)
          | exact superpose b2e200 b2e19
          | exact resolve b2e19 b2e200
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e200
        have b2e264 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e251
             have i₂ := b2e177
             grind)
          | exact superpose b2e177 b2e251
          | exact resolve b2e251 b2e177
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e177 b2e251
        have b2e265 : False := by grind
        exact b2e265
      · have b3e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e18 : y = (M.op x x) := by grind
        have b3e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b3e22 : x = (k x y) := by grind
        have b3e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X1 (τ X0)
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e16
          | exact resolve b3e16 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e37 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e19
             have i₂ := b3e15 (σ x) X0
             grind)
          | (have i₁ := b3e19
             have i₂ := b3e15 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b3e15 b3e19
          | (have j1 := b3e15 (σ x) X0
             grind)
          | (have r₁ := b3e19
             have r₂ := b3e15 (σ x) (σ y)
             grind)
          | exact resolve b3e19 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X0 X1
             have i₂ := b3e15 (σ X0) (σ X1)
             grind)
          | exact superpose b3e15 b3e16
          | (have j1 := b3e15 (σ X0) (σ X1)
             grind)
          | exact resolve b3e16 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e55 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (k X0 (τ X1))
             have i₂ := b3e24 X1 X0
             grind)
          | exact superpose b3e24 b3e12
          | exact resolve b3e12 b3e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e112 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e34 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e142 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b3e55
        have b3e156 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e142 X0
             have i₂ := b3e12 X0
             grind)
          | exact superpose b3e12 b3e142
          | exact resolve b3e142 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e142
        have b3e160 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b3e37 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e161 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e160
             have i₂ := b3e16 x y
             grind)
          | exact superpose b3e16 b3e160
          | exact resolve b3e160 b3e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e160
        have b3e162 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e161
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e161
          | exact resolve b3e161 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e22 b3e161
        have b3e163 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e17
             have i₂ := b3e162
             grind)
          | exact superpose b3e162 b3e17
          | exact resolve b3e17 b3e162
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e162
        have b3e242 : x ≠ y ∨ x = (k x x) := by
          first
          | (have i₁ := b3e112 x x
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e112
          | (have j0 := b3e112 x x
             grind)
          | exact resolve b3e112 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e112
        have b3e301 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e39 x x
             grind)
          | exact superpose b3e39 b3e19
          | (have j1 := b3e39 x x
             grind)
          | (have r₁ := b3e19
             have r₂ := b3e39 x y
             grind)
          | exact resolve b3e19 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e848 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e301
             have i₂ := b3e15 x x
             grind)
          | exact superpose b3e15 b3e301
          | (have j1 := b3e15 (σ x) (σ x)
             grind)
          | exact resolve b3e301 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e301
        have b3e849 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e848
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e848
          | exact resolve b3e848 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e848
        have b3e850 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b3e849
        have b3e861 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b3e850
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e850
          | exact resolve b3e850 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e850
        have b3e867 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b3e156 x
             have i₂ := b3e861
             grind)
          | exact superpose b3e861 b3e156
          | exact resolve b3e156 b3e861
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e156 b3e861
        have b3e884 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b3e867
             have i₂ := b3e12 x
             grind)
          | exact superpose b3e12 b3e867
          | exact resolve b3e867 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e867
        have b3e885 : x = (k x x) := by
          first
          | (have r₁ := b3e884
             have r₂ := b3e242
             grind)
          | exact resolve b3e884 b3e242
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e242 b3e884
        have b3e904 : x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e15 x x
             have i₂ := b3e885
             grind)
          | exact superpose b3e885 b3e15
          | (have j0 := b3e15 x x
             grind)
          | exact resolve b3e15 b3e885
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e885
        have b3e905 : x = (M.op x x) := by grind
        clear b3e904
        have b3e929 : x = y := by
          first
          | (have i₁ := b3e18
             have i₂ := b3e905
             grind)
          | exact superpose b3e905 b3e18
          | exact resolve b3e18 b3e905
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e905
        have b3e1062 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e163
             have i₂ := b3e929
             grind)
          | exact superpose b3e929 b3e163
          | exact resolve b3e163 b3e929
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e163
        have b3e1072 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e1062
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e1062
          | exact resolve b3e1062 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1062
        have b3e1077 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e1072
             have i₂ := b3e929
             grind)
          | exact superpose b3e929 b3e1072
          | exact resolve b3e1072 b3e929
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e929 b3e1072
        have b3e1078 : False := by grind
        exact b3e1078
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op (M.op x y) (M.op x y)) (x) with h2a | h2a
      · have b4e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b4e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b4e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b4e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b4e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b4e18 : y ≠ (M.op x x) := by grind
        have b4e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b4e20 : x = (M.op (M.op x y) (M.op x y)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b4e22 : (σ x) = (k (σ x) (σ y)) := by grind
        have b4e23 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b4e22
             have i₂ := b4e16 x y
             grind)
          | exact superpose b4e16 b4e22
          | exact resolve b4e22 b4e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e22
        have b4e25 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b4e12 (k x y)
             have i₂ := b4e23
             grind)
          | exact superpose b4e23 b4e12
          | exact resolve b4e12 b4e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e23
        have b4e26 : x = (k x y) := by
          first
          | (have i₁ := b4e25
             have i₂ := b4e12 x
             grind)
          | exact superpose b4e12 b4e25
          | exact resolve b4e25 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e25
        have b4e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b4e16 (τ X0) X1
             have i₂ := b4e13 X0
             grind)
          | exact superpose b4e13 b4e16
          | exact resolve b4e16 b4e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e41 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
          intro X0
          grind
        clear b4e27
        have b4e45 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b4e41 X0
             have i₂ := b4e13 X0
             grind)
          | exact superpose b4e13 b4e41
          | exact resolve b4e41 b4e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e41
        have b4e55 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = X0 := by
          intro X0
          first
          | (have i₁ := b4e19
             have i₂ := b4e15 (σ x) X0
             grind)
          | (have i₁ := b4e19
             have i₂ := b4e15 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b4e15 b4e19
          | (have j1 := b4e15 (σ x) X0
             grind)
          | exact resolve b4e19 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e58 : x = (M.op x y) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b4e26
             have i₂ := b4e15 x y
             grind)
          | exact superpose b4e15 b4e26
          | (have j1 := b4e15 x y
             grind)
          | exact resolve b4e26 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e26
        have b4e61 : x = (M.op x y) := by
          first
          | (have r₁ := b4e58
             have r₂ := b4e18
             grind)
          | exact resolve b4e58 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e58
        have b4e64 : x = (M.op x x) := by
          first
          | (have i₁ := b4e20
             have i₂ := b4e61
             grind)
          | exact superpose b4e61 b4e20
          | exact resolve b4e20 b4e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e61
        have b4e112 : x ≠ y := by
          first
          | (have i₁ := b4e18
             have i₂ := b4e64
             grind)
          | exact superpose b4e64 b4e18
          | exact resolve b4e18 b4e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e225 : (σ x) = (M.op (σ x) (σ (M.op (τ (σ x)) (τ (σ x))))) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e45 (σ x)
             have i₂ := b4e55 (σ (M.op (τ (σ x)) (τ (σ x))))
             grind)
          | exact superpose b4e55 b4e45
          | (have j1 := b4e55 (σ (M.op (τ (σ x)) (τ (σ x))))
             grind)
          | exact resolve b4e45 b4e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e45 b4e55
        have b4e227 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e225
             have i₂ := b4e12 x
             grind)
          | exact superpose b4e12 b4e225
          | exact resolve b4e225 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e225
        have b4e230 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e227
             have i₂ := b4e64
             grind)
          | exact superpose b4e64 b4e227
          | exact resolve b4e227 b4e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e227
        have b4e232 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e230
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e230
          | exact resolve b4e230 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e230
        have b4e234 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b4e232
             have i₂ := b4e12 x
             grind)
          | exact superpose b4e12 b4e232
          | exact resolve b4e232 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e232
        have b4e236 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b4e234
             have i₂ := b4e64
             grind)
          | exact superpose b4e64 b4e234
          | exact resolve b4e234 b4e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e64 b4e234
        have b4e237 : (σ x) = (σ y) := by grind
        clear b4e236
        have b4e244 : y = (τ (σ x)) := by
          first
          | (have i₁ := b4e12 y
             have i₂ := b4e237
             grind)
          | exact superpose b4e237 b4e12
          | exact resolve b4e12 b4e237
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e237
        have b4e245 : x = y := by
          first
          | (have i₁ := b4e244
             have i₂ := b4e12 x
             grind)
          | exact superpose b4e12 b4e244
          | exact resolve b4e244 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e244
        have b4e250 : False := by grind
        exact b4e250
      · have b5e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b5e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b5e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b5e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b5e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b5e18 : y ≠ (M.op x x) := by grind
        have b5e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b5e20 : x ≠ (M.op (M.op x y) (M.op x y)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b5e22 : (σ x) = (k (σ x) (σ y)) := by grind
        have b5e23 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b5e22
             have i₂ := b5e16 x y
             grind)
          | exact superpose b5e16 b5e22
          | exact resolve b5e22 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e22
        have b5e24 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b5e12 (k x y)
             have i₂ := b5e23
             grind)
          | exact superpose b5e23 b5e12
          | exact resolve b5e12 b5e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e25 : x = (k x y) := by
          first
          | (have i₁ := b5e24
             have i₂ := b5e12 x
             grind)
          | exact superpose b5e12 b5e24
          | exact resolve b5e24 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e24
        have b5e57 : ∀ X0 : G, x ≠ X0 ∨ (k (M.op x y) X0) = (M.op (M.op x y) X0) := by
          intro X0
          first
          | (have i₁ := b5e20
             have i₂ := b5e15 (M.op x y) X0
             grind)
          | (have i₁ := b5e20
             have i₂ := b5e15 X0 (M.op (M.op x y) (M.op x y))
             grind)
          | exact superpose b5e15 b5e20
          | (have j1 := b5e15 (M.op x y) X0
             grind)
          | (have r₁ := b5e20
             have r₂ := b5e15 (M.op x y) x
             grind)
          | exact resolve b5e20 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b5e16 X0 X1
             have i₂ := b5e15 (σ X0) (σ X1)
             grind)
          | exact superpose b5e15 b5e16
          | (have j1 := b5e15 (σ X0) (σ X1)
             grind)
          | exact resolve b5e16 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e62 : x = (M.op x y) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b5e25
             have i₂ := b5e15 x y
             grind)
          | exact superpose b5e15 b5e25
          | (have j1 := b5e15 x y
             grind)
          | exact resolve b5e25 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e25
        have b5e63 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b5e23
             have i₂ := b5e15 x y
             grind)
          | exact superpose b5e15 b5e23
          | (have j1 := b5e15 x y
             grind)
          | exact resolve b5e23 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e23
        have b5e64 : (σ (M.op x y)) = (σ x) := by
          first
          | (have r₁ := b5e63
             have r₂ := b5e18
             grind)
          | exact resolve b5e63 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e63
        have b5e65 : x = (M.op x y) := by
          first
          | (have r₁ := b5e62
             have r₂ := b5e18
             grind)
          | exact resolve b5e62 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e62
        have b5e252 : (k (M.op x y) x) = (M.op (M.op x y) x) := by
          first
          | (have j0 := b5e57 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e57
        have b5e253 : (M.op x x) = (k x x) := by
          first
          | (have i₁ := b5e252
             have i₂ := b5e65
             grind)
          | exact superpose b5e65 b5e252
          | exact resolve b5e252 b5e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e65 b5e252
        have b5e407 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e60 x x
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e60
          | exact resolve b5e60 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e60
        have b5e476 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e407
             have i₂ := b5e253
             grind)
          | exact superpose b5e253 b5e407
          | exact resolve b5e407 b5e253
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e253 b5e407
        have b5e487 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e12 (M.op x x)
             have i₂ := b5e476
             grind)
          | exact superpose b5e476 b5e12
          | exact resolve b5e12 b5e476
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e476
        have b5e500 : y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e487
             have i₂ := b5e12 y
             grind)
          | exact superpose b5e12 b5e487
          | exact resolve b5e487 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e487
        have b5e501 : (σ x) = (σ y) := by
          first
          | (have r₁ := b5e500
             have r₂ := b5e18
             grind)
          | exact resolve b5e500 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e500
        have b5e560 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b5e17
             have i₂ := b5e501
             grind)
          | exact superpose b5e501 b5e17
          | exact resolve b5e17 b5e501
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e578 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b5e560
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e560
          | exact resolve b5e560 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e560
        have b5e582 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b5e578
             have i₂ := b5e501
             grind)
          | exact superpose b5e501 b5e578
          | exact resolve b5e578 b5e501
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e501 b5e578
        have b5e586 : False := by grind
        exact b5e586
    · rcases eq_or_ne (M.op (M.op x y) (M.op x y)) (x) with h2a | h2a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e18 : y ≠ (M.op x x) := by grind
        have b6e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b6e43 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e19
             have i₂ := b6e15 (σ x) X0
             grind)
          | (have i₁ := b6e19
             have i₂ := b6e15 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b6e15 b6e19
          | (have j1 := b6e15 (σ x) X0
             grind)
          | (have r₁ := b6e19
             have r₂ := b6e15 (σ x) (σ y)
             grind)
          | exact resolve b6e19 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e156 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b6e43 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e157 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e156
             have i₂ := b6e16 x y
             grind)
          | exact superpose b6e16 b6e156
          | exact resolve b6e156 b6e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e156
        have b6e158 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e17
             have i₂ := b6e157
             grind)
          | exact superpose b6e157 b6e17
          | exact resolve b6e17 b6e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e157
        have b6e178 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e158
             have i₂ := b6e15 x y
             grind)
          | exact superpose b6e15 b6e158
          | (have j1 := b6e15 x y
             grind)
          | exact resolve b6e158 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e158
        have b6e179 : y = (M.op x x) := by grind
        clear b6e178
        have b6e182 : False := by grind
        exact b6e182
      · have b7e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b7e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b7e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b7e18 : y ≠ (M.op x x) := by grind
        have b7e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b7e46 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b7e19
             have i₂ := b7e15 (σ x) X0
             grind)
          | (have i₁ := b7e19
             have i₂ := b7e15 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b7e15 b7e19
          | (have j1 := b7e15 (σ x) X0
             grind)
          | (have r₁ := b7e19
             have r₂ := b7e15 (σ x) (σ y)
             grind)
          | exact resolve b7e19 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e139 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b7e46 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e46
        have b7e140 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b7e139
             have i₂ := b7e16 x y
             grind)
          | exact superpose b7e16 b7e139
          | exact resolve b7e139 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e139
        have b7e141 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e140
             grind)
          | exact superpose b7e140 b7e17
          | exact resolve b7e17 b7e140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e140
        have b7e159 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b7e141
             have i₂ := b7e15 x y
             grind)
          | exact superpose b7e15 b7e141
          | (have j1 := b7e15 x y
             grind)
          | exact resolve b7e141 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e141
        have b7e160 : y = (M.op x x) := by grind
        clear b7e159
        have b7e163 : False := by grind
        exact b7e163

/-- `Equation4385`: `x ◇ (x ◇ x) = (y ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation4385 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4385 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4385.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X0) := by
        intro X0 X1
        grind
      have b0e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : x = (M.op y y) := by grind
      have b0e18 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e20 : y = (k x y) := by grind
      have b0e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 (τ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (k (τ X0) X1)
           have i₂ := b0e23 X0 X1
           grind)
        | exact superpose b0e23 b0e11
        | exact resolve b0e11 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e29 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (σ y) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e10 (σ y) X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X1) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 X2
           have i₂ := b0e10 X1 X0
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e10 (σ y) (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e10 y y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : (M.op y (M.op y y)) = (M.op (M.op y x) y) := by
        first
        | (have i₁ := b0e10 y x
           have i₂ := b0e33
           grind)
        | exact superpose b0e33 b0e10
        | exact resolve b0e10 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : (M.op y x) = (M.op (M.op y x) y) := by
        first
        | (have i₁ := b0e34
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e34
        | exact resolve b0e34 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e41 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X0 X1
           have i₂ := b0e14 (σ X0) (σ X1)
           grind)
        | exact superpose b0e14 b0e15
        | (have j1 := b0e14 (σ X0) (σ X1)
           grind)
        | exact resolve b0e15 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e23 X0 X1
           have i₂ := b0e14 (τ X0) X1
           grind)
        | exact superpose b0e14 b0e23
        | (have j1 := b0e14 (τ X0) X1
           grind)
        | exact resolve b0e23 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e56 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (k X0 (τ X1))
           have i₂ := b0e24 X1 X0
           grind)
        | exact superpose b0e24 b0e11
        | exact resolve b0e11 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e60 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e28 X1 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e28
        | exact resolve b0e28 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e64 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
        intro X0
        grind
      have b0e70 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e64 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e64
        | exact resolve b0e64 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e64
      have b0e84 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e30 X1 X2 X2
           have i₂ := b0e14 X0 X2
           grind)
        | (have i₁ := b0e30 X0 X1 X2
           have i₂ := b0e14 (M.op X2 X1) X1
           grind)
        | exact superpose b0e14 b0e30
        | (have j1 := b0e14 X0 X2
           grind)
        | exact resolve b0e30 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e126 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e32
           grind)
        | exact superpose b0e32 b0e16
        | exact resolve b0e16 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e133 : (M.op (σ y) (σ x)) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b0e126
           have i₂ := b0e33
           grind)
        | exact superpose b0e33 b0e126
        | exact resolve b0e126 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e126
      have b0e155 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e41 (σ X0) (σ X1)
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e41
        | exact resolve b0e41 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e164 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e41 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e191 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ X1 ∨ (k (M.op X2 X1) X1) = X1 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e164 (M.op X2 X1) X1
           have i₂ := b0e30 X2 X1 X0
           grind)
        | (have i₁ := b0e164 (M.op X2 X1) X1
           have i₂ := b0e30 X0 X1 X2
           grind)
        | exact superpose b0e30 b0e164
        | (have j0 := b0e164 (M.op X0 X1) X1
           grind)
        | exact resolve b0e164 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e388 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e44 y y
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e44
        | exact resolve b0e44 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e391 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e44 X0 X0
           have i₂ := b0e14 X0 (σ X0)
           grind)
        | (have i₁ := b0e44 X0 X1
           have i₂ := b0e14 (M.op (σ X0) (σ X1)) X1
           grind)
        | exact superpose b0e14 b0e44
        | (have j1 := b0e14 X0 (σ X1)
           grind)
        | exact resolve b0e44 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e409 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (k X0 y)) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e29 (σ X0)
           have i₂ := b0e44 X0 y
           grind)
        | exact superpose b0e44 b0e29
        | (have j1 := b0e44 X0 y
           grind)
        | exact resolve b0e29 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e420 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1
           have i₂ := b0e44 X1 X0
           grind)
        | exact superpose b0e44 b0e11
        | (have j1 := b0e44 X1 X0
           grind)
        | exact resolve b0e11 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e421 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op (σ X0) (σ X0)) (σ X2)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X1 X2
           have i₂ := b0e44 X1 X0
           grind)
        | exact superpose b0e44 b0e15
        | (have j1 := b0e44 X1 X0
           grind)
        | exact resolve b0e15 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e442 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e44 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e452 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (k X0 y)) (σ y)) ∨ (σ X0) = (σ x) := by
        intro X0
        first
        | (have i₁ := b0e409 X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e409
        | (have j0 := b0e409 X0
           grind)
        | exact resolve b0e409 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e409
      have b0e465 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e11 (k y y)
           have i₂ := b0e388
           grind)
        | exact superpose b0e388 b0e11
        | exact resolve b0e11 b0e388
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e388
      have b0e478 : x = (k y y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e465
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e465
        | exact resolve b0e465 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e465
      have b0e1157 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e442 (τ X0)
           have i₂ := b0e23 X0 (τ X0)
           grind)
        | exact superpose b0e23 b0e442
        | (have j0 := b0e442 (τ X0)
           grind)
        | exact resolve b0e442 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e442
      have b0e1160 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e1157 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e1157
        | (have j0 := b0e1157 X0
           grind)
        | exact resolve b0e1157 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1157
      have b0e1166 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e1160 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e1160
        | (have j0 := b0e1160 X0
           grind)
        | exact resolve b0e1160 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1160
      have b0e1195 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e45 (σ X0) X1
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e45
        | exact resolve b0e45 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1224 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 X1
           have i₂ := b0e45 X1 X0
           grind)
        | exact superpose b0e45 b0e12
        | (have j1 := b0e45 X1 X0
           grind)
        | exact resolve b0e12 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e1272 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e1195 X0 X1
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e1195
        | (have j0 := b0e1195 X0 X1
           grind)
        | exact resolve b0e1195 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1195
      have b0e1436 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X1 x
           have i₂ := b0e84 X0 x X1
           grind)
        | (have i₁ := b0e10 x X1
           have i₂ := b0e84 (M.op X1 x) X1 x
           grind)
        | exact superpose b0e84 b0e10
        | (have j1 := b0e84 X0 X1 X1
           grind)
        | exact resolve b0e10 b0e84
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e84
      have b0e2161 : (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e155 y y
           grind)
        | exact superpose b0e155 b0e18
        | (have j1 := b0e155 y y
           grind)
        | exact resolve b0e18 b0e155
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e155
      have b0e2221 : (k y y) = (τ (σ x)) ∨ (σ y) = (σ (k y y)) := by
        first
        | (have i₁ := b0e11 (k y y)
           have i₂ := b0e2161
           grind)
        | exact superpose b0e2161 b0e11
        | exact resolve b0e11 b0e2161
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2161
      have b0e2254 : (σ y) = (σ (k y y)) ∨ x = (k y y) := by
        first
        | (have i₁ := b0e2221
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e2221
        | exact resolve b0e2221 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2221
      have b0e3079 : ∀ X0 : G, (τ (σ x)) = X0 ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e420 y X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e420
        | (have j0 := b0e420 y X0
           grind)
        | exact resolve b0e420 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e3086 : ∀ X0 X1 X2 : G, (τ X0) = X2 ∨ (M.op (σ X2) (σ X1)) = (σ (k X2 X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e420 X1 X2
           have i₂ := b0e14 X0 (σ X1)
           grind)
        | (have i₁ := b0e420 X0 X1
           have i₂ := b0e14 (M.op (σ X0) (σ X0)) X1
           grind)
        | exact superpose b0e14 b0e420
        | (have j0 := b0e420 X1 X2
           have j1 := b0e14 X0 (σ X1)
           grind)
        | exact resolve b0e420 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e3113 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e420 (τ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e420
        | exact resolve b0e420 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e3124 : (σ x) = (σ (k y y)) ∨ y = (τ (σ x)) := by
        first
        | (have i₁ := b0e420 y y
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e420
        | exact resolve b0e420 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e3150 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (k X0 y)) (σ y)) ∨ (τ (M.op (σ y) (σ y))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e29 (σ X0)
           have i₂ := b0e420 y X0
           grind)
        | exact superpose b0e420 b0e29
        | (have j1 := b0e420 y X0
           grind)
        | exact resolve b0e29 b0e420
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e3173 : ∀ X0 : G, (τ (σ x)) = X0 ∨ (M.op (σ y) (σ x)) = (M.op (σ (k X0 y)) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e3150 X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e3150
        | (have j0 := b0e3150 X0
           grind)
        | exact resolve b0e3150 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3150
      have b0e3180 : (σ x) = (σ (k y y)) ∨ x = y := by
        first
        | (have i₁ := b0e3124
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e3124
        | exact resolve b0e3124 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3124
      have b0e3183 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e3113 X0 X1
           have i₂ := b0e24 X0 X1
           grind)
        | exact superpose b0e24 b0e3113
        | (have j0 := b0e3113 X0 X1
           grind)
        | exact resolve b0e3113 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3113
      have b0e3190 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ x = X0 := by
        intro X0
        first
        | (have i₁ := b0e3079 X0
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e3079
        | (have j0 := b0e3079 X0
           grind)
        | exact resolve b0e3079 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3079
      have b0e3194 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (k X0 y)) (σ y)) ∨ x = X0 := by
        intro X0
        first
        | (have i₁ := b0e3173 X0
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e3173
        | (have j0 := b0e3173 X0
           grind)
        | exact resolve b0e3173 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3173
      have b0e3213 : (k y y) = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e11 (k y y)
           have i₂ := b0e3180
           grind)
        | exact superpose b0e3180 b0e11
        | exact resolve b0e11 b0e3180
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3180
      have b0e3249 : x = (k y y) ∨ x = y := by
        first
        | (have i₁ := b0e3213
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e3213
        | exact resolve b0e3213 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3213
      have b0e3295 : ∀ X0 : G, (M.op (σ y) (σ x)) = (σ (k (k X0 y) y)) ∨ (k X0 y) = (τ (M.op (σ y) (σ y))) ∨ (σ X0) = (σ x) := by
        intro X0
        first
        | (have i₁ := b0e420 y (k X0 y)
           have i₂ := b0e452 X0
           grind)
        | exact superpose b0e452 b0e420
        | (have j0 := b0e420 y (k X0 y)
           have j1 := b0e452 X0
           grind)
        | exact resolve b0e420 b0e452
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e452
      have b0e3327 : ∀ X0 : G, (k X0 y) = (τ (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k (k X0 y) y)) ∨ (σ X0) = (σ x) := by
        intro X0
        first
        | (have i₁ := b0e3295 X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e3295
        | (have j0 := b0e3295 X0
           grind)
        | exact resolve b0e3295 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3295
      have b0e3347 : ∀ X0 : G, (M.op (σ y) (σ x)) = (σ (k (k X0 y) y)) ∨ x = (k X0 y) ∨ (σ X0) = (σ x) := by
        intro X0
        first
        | (have i₁ := b0e3327 X0
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e3327
        | (have j0 := b0e3327 X0
           grind)
        | exact resolve b0e3327 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3327
      have b0e3558 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (k (τ X0) y)) ∨ (τ X0) = x := by
        intro X0
        first
        | (have i₁ := b0e3190 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e3190
        | (have j0 := b0e3190 (τ X0)
           grind)
        | exact resolve b0e3190 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e3579 : y = (k (τ (σ (k y y))) y) ∨ x = y := by
        first
        | (have i₁ := b0e70 y
           have i₂ := b0e3190 y
           grind)
        | exact superpose b0e3190 b0e70
        | (have j1 := b0e3190 y
           grind)
        | exact resolve b0e70 b0e3190
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70 b0e3190
      have b0e3620 : y = (k (k y y) y) ∨ x = y := by
        first
        | (have i₁ := b0e3579
           have i₂ := b0e11 (k y y)
           grind)
        | exact superpose b0e11 b0e3579
        | exact resolve b0e3579 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3579
      have b0e3625 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (τ X0) = x := by
        intro X0
        first
        | (have i₁ := b0e3558 X0
           have i₂ := b0e23 X0 y
           grind)
        | exact superpose b0e23 b0e3558
        | (have j0 := b0e3558 X0
           grind)
        | exact resolve b0e3558 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3558
      have b0e4056 : ∀ X0 : G, (k X0 (τ (σ y))) = (τ (M.op (σ X0) (σ y))) ∨ (τ (σ X0)) = x := by
        intro X0
        first
        | (have i₁ := b0e56 X0 (σ y)
           have i₂ := b0e3625 (σ X0)
           grind)
        | exact superpose b0e3625 b0e56
        | (have j1 := b0e3625 (σ X0)
           grind)
        | exact resolve b0e56 b0e3625
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56 b0e3625
      have b0e4080 : ∀ X0 : G, (k X0 y) = (τ (M.op (σ X0) (σ y))) ∨ (τ (σ X0)) = x := by
        intro X0
        first
        | (have i₁ := b0e4056 X0
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e4056
        | (have j0 := b0e4056 X0
           grind)
        | exact resolve b0e4056 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4056
      have b0e4104 : ∀ X0 : G, (k X0 y) = (τ (M.op (σ X0) (σ y))) ∨ x = X0 := by
        intro X0
        first
        | (have i₁ := b0e4080 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e4080
        | (have j0 := b0e4080 X0
           grind)
        | exact resolve b0e4080 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4080
      have b0e4303 : (τ (M.op (σ y) (σ y))) = (k (k y y) y) ∨ x = (k y y) ∨ x = (k y y) := by
        first
        | (have i₁ := b0e4104 (k y y)
           have i₂ := b0e2254
           grind)
        | exact superpose b0e2254 b0e4104
        | (have j0 := b0e4104 (k y y)
           grind)
        | exact resolve b0e4104 b0e2254
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2254 b0e4104
      have b0e4339 : (τ (M.op (σ y) (σ y))) = (k (k y y) y) ∨ x = (k y y) := by grind
      clear b0e4303
      have b0e4343 : (τ (σ x)) = (k (k y y) y) ∨ x = (k y y) := by
        first
        | (have i₁ := b0e4339
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e4339
        | exact resolve b0e4339 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4339
      have b0e4347 : x = (k (k y y) y) ∨ x = (k y y) := by
        first
        | (have i₁ := b0e4343
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e4343
        | exact resolve b0e4343 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4343
      have b0e4358 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e391 X0 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e391
        | (have j0 := b0e391 X1 (τ X0)
           grind)
        | exact resolve b0e391 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e391
      have b0e4476 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e4358 X0 X1
           have i₂ := b0e24 X0 (τ X0)
           grind)
        | exact superpose b0e24 b0e4358
        | (have j0 := b0e4358 X0 X1
           grind)
        | exact resolve b0e4358 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4358
      have b0e4489 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e4476 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e4476
        | (have j0 := b0e4476 X0 X1
           grind)
        | exact resolve b0e4476 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4476
      have b0e4537 : x = (M.op (k y y) y) ∨ (M.op y y) = (k y y) ∨ x = (k y y) := by
        first
        | (have i₁ := b0e14 (k y y) y
           have i₂ := b0e4347
           grind)
        | exact superpose b0e4347 b0e14
        | (have j0 := b0e14 (k y y) y
           grind)
        | exact resolve b0e14 b0e4347
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4347
      have b0e4557 : x = (k y y) ∨ x = (M.op (k y y) y) ∨ x = (k y y) := by
        first
        | (have i₁ := b0e4537
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e4537
        | exact resolve b0e4537 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4537
      have b0e4558 : x = (M.op (k y y) y) ∨ x = (k y y) := by grind
      clear b0e4557
      have b0e4805 : x ≠ y ∨ y = (k (k y y) y) ∨ x = (k y y) := by
        first
        | (have i₁ := b0e164 (k y y) y
           have i₂ := b0e4558
           grind)
        | exact superpose b0e4558 b0e164
        | (have j0 := b0e164 (k y y) y
           grind)
        | exact resolve b0e164 b0e4558
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e164 b0e4558
      have b0e4816 : y = (k (k y y) y) ∨ x = (k y y) := by
        first
        | (have r₁ := b0e4805
           have r₂ := b0e3620
           grind)
        | exact resolve b0e4805 b0e3620
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3620 b0e4805
      have b0e5036 : y = (M.op (k y y) y) ∨ (M.op y y) = (k y y) ∨ x = (k y y) := by
        first
        | (have i₁ := b0e14 (k y y) y
           have i₂ := b0e4816
           grind)
        | exact superpose b0e4816 b0e14
        | (have j0 := b0e14 (k y y) y
           grind)
        | exact resolve b0e14 b0e4816
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e5053 : x = (k y y) ∨ y = (M.op (k y y) y) ∨ x = (k y y) := by
        first
        | (have i₁ := b0e5036
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e5036
        | exact resolve b0e5036 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5036
      have b0e5054 : y = (M.op (k y y) y) ∨ x = (k y y) := by grind
      clear b0e5053
      have b0e5320 : ∀ X0 : G, y ≠ (M.op y y) ∨ y = (k (M.op X0 y) y) ∨ x = (k y y) := by
        intro X0
        first
        | (have i₁ := b0e191 (k y y) y X0
           have i₂ := b0e5054
           grind)
        | exact superpose b0e5054 b0e191
        | (have j0 := b0e191 X0 y X0
           grind)
        | exact resolve b0e191 b0e5054
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e191 b0e5054
      have b0e5336 : ∀ X0 : G, x ≠ y ∨ y = (k (M.op X0 y) y) ∨ x = (k y y) := by
        intro X0
        first
        | (have i₁ := b0e5320 X0
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e5320
        | (have j0 := b0e5320 X0
           grind)
        | exact resolve b0e5320 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5320
      have b0e5345 : ∀ X0 : G, y = (k (M.op X0 y) y) ∨ x = (k y y) := by
        intro X0
        first
        | (have j0 := b0e5336 X0
           grind)
        | (have r₁ := b0e5336 X0
           have r₂ := b0e3249
           grind)
        | exact resolve b0e5336 b0e3249
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3249 b0e5336
      have b0e5503 : y = (k (M.op y x) y) ∨ x = (k y y) := by
        first
        | (have i₁ := b0e5345 x
           have i₂ := b0e33
           grind)
        | exact superpose b0e33 b0e5345
        | exact resolve b0e5345 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5345
      have b0e12038 : ∀ X0 X1 X2 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e421 (τ X0) X1 X2
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e421
        | exact resolve b0e421 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e421
      have b0e12243 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e12038 X0 X1 X2
           have i₂ := b0e24 X0 X1
           grind)
        | exact superpose b0e24 b0e12038
        | (have j0 := b0e12038 X0 X1 X2
           grind)
        | exact resolve b0e12038 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24 b0e12038
      have b0e27763 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (τ X0) = (τ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e3183 X0 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e3183
        | (have j0 := b0e3183 X1 (τ X0)
           grind)
        | exact resolve b0e3183 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3183
      have b0e28412 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e4489 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32553 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (σ (M.op X1 X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (M.op (τ X0) X1)
           have i₂ := b0e1224 X1 X0
           grind)
        | exact superpose b0e1224 b0e11
        | (have j1 := b0e1224 X1 X0
           grind)
        | exact resolve b0e11 b0e1224
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1224
      have b0e32675 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (σ (M.op X1 X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e32553 X0 X1
           have i₂ := b0e28 X0 X1
           grind)
        | exact superpose b0e28 b0e32553
        | (have j0 := b0e32553 X0 X1
           grind)
        | exact resolve b0e32553 b0e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28 b0e32553
      have b0e33701 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (k y y) ∨ x = (k y y) := by
        first
        | (have i₁ := b0e3194 (k y y)
           have i₂ := b0e4816
           grind)
        | exact superpose b0e4816 b0e3194
        | (have j0 := b0e3194 (k y y)
           grind)
        | exact resolve b0e3194 b0e4816
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3194 b0e4816
      have b0e33852 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (k y y) := by grind
      clear b0e33701
      have b0e33918 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k y y) := by
        first
        | (have i₁ := b0e33852
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e33852
        | exact resolve b0e33852 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33852
      have b0e36790 : (σ x) ≠ (σ (M.op y x)) ∨ x = (k y y) := by
        first
        | (have i₁ := b0e133
           have i₂ := b0e33918
           grind)
        | exact superpose b0e33918 b0e133
        | exact resolve b0e133 b0e33918
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33918
      have b0e49749 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e32675 (σ X0) X1
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e32675
        | (have j0 := b0e32675 (σ X0) X1
           grind)
        | exact resolve b0e32675 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32675
      have b0e50349 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (σ X0) = (σ x) := by
        intro X0
        first
        | (have i₁ := b0e49749 X0 y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e49749
        | (have j0 := b0e49749 X0 y
           grind)
        | exact resolve b0e49749 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49749
      have b0e52054 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op (τ X0) y)) ∨ (σ (τ X0)) = (σ x) := by
        intro X0
        first
        | (have i₁ := b0e23 X0 y
           have i₂ := b0e50349 (τ X0)
           grind)
        | exact superpose b0e50349 b0e23
        | (have j1 := b0e50349 (τ X0)
           grind)
        | exact resolve b0e23 b0e50349
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e50349
      have b0e52168 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op (τ X0) y)) ∨ (σ x) = X0 := by
        intro X0
        first
        | (have i₁ := b0e52054 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e52054
        | (have j0 := b0e52054 X0
           grind)
        | exact resolve b0e52054 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52054
      have b0e52979 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ (σ X0) = (σ x) := by
        intro X0
        first
        | (have i₁ := b0e52168 (σ X0)
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e52168
        | (have j0 := b0e52168 (σ X0)
           grind)
        | exact resolve b0e52168 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52168
      have b0e53158 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 y)) ∨ (σ X0) = (σ x) := by
        intro X0
        first
        | (have i₁ := b0e52979 X0
           have i₂ := b0e15 X0 y
           grind)
        | exact superpose b0e15 b0e52979
        | (have j0 := b0e52979 X0
           grind)
        | exact resolve b0e52979 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52979
      have b0e54802 : (σ y) = (σ (M.op (M.op y x) y)) ∨ (σ x) = (σ (M.op y x)) ∨ x = (k y y) := by
        first
        | (have i₁ := b0e53158 (M.op y x)
           have i₂ := b0e5503
           grind)
        | exact superpose b0e5503 b0e53158
        | (have j0 := b0e53158 (M.op y x)
           grind)
        | exact resolve b0e53158 b0e5503
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5503 b0e53158
      have b0e55087 : (σ y) = (σ (M.op (M.op y x) y)) ∨ x = (k y y) := by
        first
        | (have r₁ := b0e54802
           have r₂ := b0e36790
           grind)
        | exact resolve b0e54802 b0e36790
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54802
      have b0e55092 : (σ y) = (σ (M.op y x)) ∨ x = (k y y) := by
        first
        | (have i₁ := b0e55087
           have i₂ := b0e35
           grind)
        | exact superpose b0e35 b0e55087
        | exact resolve b0e55087 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55087
      have b0e56008 : (σ x) ≠ (σ y) ∨ x = (k y y) ∨ x = (k y y) := by
        first
        | (have i₁ := b0e36790
           have i₂ := b0e55092
           grind)
        | exact superpose b0e55092 b0e36790
        | exact resolve b0e36790 b0e55092
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36790 b0e55092
      have b0e56134 : (σ x) ≠ (σ y) ∨ x = (k y y) := by grind
      clear b0e56008
      have b0e56194 : x = (k y y) := by
        first
        | (have r₁ := b0e56134
           have r₂ := b0e478
           grind)
        | exact resolve b0e56134 b0e478
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e478 b0e56134
      have b0e56615 : ∀ X0 : G, x ≠ y ∨ (M.op X0 y) = (k X0 y) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e28412 X0 y
           have i₂ := b0e56194
           grind)
        | exact superpose b0e56194 b0e28412
        | (have j0 := b0e28412 X0 y
           grind)
        | exact resolve b0e28412 b0e56194
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28412 b0e56194
      have b0e91209 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) (σ (τ X1))) ∨ (k (σ (τ X0)) X2) = (M.op (σ (τ X0)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e12243 X2 (τ X0) (τ X1)
           have i₂ := b0e60 X1 X0
           grind)
        | exact superpose b0e60 b0e12243
        | (have j0 := b0e12243 X2 (τ X0) X2
           grind)
        | exact resolve b0e12243 b0e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12243
      have b0e91999 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) X1) ∨ (k (σ (τ X0)) X2) = (M.op (σ (τ X0)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e91209 X0 X1 X2
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e91209
        | (have j0 := b0e91209 X0 X1 X2
           grind)
        | exact resolve b0e91209 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e91209
      have b0e92103 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X2 X2) X1) ∨ (k (σ (τ X0)) X2) = (M.op (σ (τ X0)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e91999 X0 X1 X2
           have i₂ := b0e12 (k X0 X1)
           grind)
        | exact superpose b0e12 b0e91999
        | (have j0 := b0e91999 X0 X1 X2
           grind)
        | exact resolve b0e91999 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e91999
      have b0e92125 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (k X0 X1) = (k (M.op X2 X2) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e92103 X0 X1 X2
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e92103
        | (have j0 := b0e92103 X0 X1 X2
           grind)
        | exact resolve b0e92103 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e92103
      have b0e110827 : ∀ X0 X1 : G, (k X0 X1) = (k x X1) ∨ (M.op X0 y) = (k X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e92125 X0 X1 y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e92125
        | (have j0 := b0e92125 X0 X1 y
           grind)
        | exact resolve b0e92125 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e111081 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e92125 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e111082 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      clear b0e111081
      have b0e111268 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e111082 X1 X1
           have i₂ := b0e14 X0 X1
           grind)
        | (have i₁ := b0e111082 X0 X1
           have i₂ := b0e14 (M.op X0 X1) X1
           grind)
        | exact superpose b0e14 b0e111082
        | (have j0 := b0e111082 X0 X1
           have j1 := b0e14 X0 X1
           grind)
        | (have r₁ := b0e111082 X0 X0
           have r₂ := b0e14 X0 X0
           grind)
        | (have r₁ := b0e111082 X0 (M.op X1 X1)
           have r₂ := b0e14 (M.op X0 (M.op X1 X1)) X1
           grind)
        | exact resolve b0e111082 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e111307 : y ≠ (M.op y x) ∨ (M.op y x) = (k (M.op y x) y) := by
        first
        | (have i₁ := b0e111082 (M.op y x) y
           have i₂ := b0e35
           grind)
        | exact superpose b0e35 b0e111082
        | exact resolve b0e111082 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e111380 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e111268 X0 X1
           have j1 := b0e4489 X1 X0
           grind)
        | (have r₁ := b0e111268 (M.op X1 X0) (k X1 X0)
           have r₂ := b0e4489 X0 X1
           grind)
        | (have r₁ := b0e111268 (k X1 X0) (M.op X1 X0)
           have r₂ := b0e4489 X0 X1
           grind)
        | (have r₁ := b0e111268 (k X0 X0) X1
           have r₂ := b0e4489 X0 X1
           grind)
        | exact resolve b0e111268 b0e4489
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4489 b0e111268
      have b0e111780 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        grind
      clear b0e111380
      have b0e111935 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e111780 X0
           have i₂ := b0e10 X0 X0
           grind)
        | exact superpose b0e10 b0e111780
        | (have j0 := b0e111780 X0
           grind)
        | exact resolve b0e111780 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e111780
      have b0e113507 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e1436 X1 X0
           have i₂ := b0e111935 X0
           grind)
        | exact superpose b0e111935 b0e1436
        | (have j0 := b0e1436 X1 X0
           have j1 := b0e111935 X0
           grind)
        | exact resolve b0e1436 b0e111935
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1436 b0e111935
      have b0e113539 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e113507 X0 X1
           have j1 := b0e111082 X1 X0
           grind)
        | (have r₁ := b0e113507 X1 X0
           have r₂ := b0e111082 X0 X1
           grind)
        | exact resolve b0e113507 b0e111082
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e111082 b0e113507
      have b0e114466 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e113539 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e113539
      have b0e114467 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e114466 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e114466
      have b0e114666 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e15 X0 X0
           have i₂ := b0e114467 (σ X0)
           grind)
        | exact superpose b0e114467 b0e15
        | exact resolve b0e15 b0e114467
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e114678 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e60 X0 X0
           have i₂ := b0e114467 (τ X0)
           grind)
        | exact superpose b0e114467 b0e60
        | exact resolve b0e60 b0e114467
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60
      have b0e114705 : ∀ X0 : G, (k X0 x) = (M.op x x) ∨ (M.op X0 y) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b0e110827 X0 x
           have i₂ := b0e114467 x
           grind)
        | exact superpose b0e114467 b0e110827
        | (have j0 := b0e110827 X0 x
           grind)
        | exact resolve b0e110827 b0e114467
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e110827
      have b0e114798 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e114678 X0
           have i₂ := b0e114467 X0
           grind)
        | exact superpose b0e114467 b0e114678
        | exact resolve b0e114678 b0e114467
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e114678
      have b0e114808 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e114666 X0
           have i₂ := b0e114467 X0
           grind)
        | exact superpose b0e114467 b0e114666
        | exact resolve b0e114666 b0e114467
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e114666
      have b0e115069 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 (τ X0)
           have i₂ := b0e114798 X0
           grind)
        | exact superpose b0e114798 b0e14
        | (have j0 := b0e14 X1 (τ X0)
           grind)
        | exact resolve b0e14 b0e114798
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e114798
      have b0e115399 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e420 X0 X1
           have i₂ := b0e114808 X0
           grind)
        | exact superpose b0e114808 b0e420
        | (have j0 := b0e420 X0 X1
           grind)
        | exact resolve b0e420 b0e114808
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e420
      have b0e115498 : ∀ X0 X1 : G, (τ X1) = (τ (σ (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e27763 X1 (σ X0)
           have i₂ := b0e114808 X0
           grind)
        | exact superpose b0e114808 b0e27763
        | (have j0 := b0e27763 X1 (σ X0)
           grind)
        | exact resolve b0e27763 b0e114808
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27763
      have b0e115569 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e115498 X0 X1
           have i₂ := b0e11 (M.op X0 X0)
           grind)
        | exact superpose b0e11 b0e115498
        | (have j0 := b0e115498 X0 X1
           grind)
        | exact resolve b0e115498 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e115498
      have b0e115624 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e115399 X0 X1
           have i₂ := b0e11 (M.op X0 X0)
           grind)
        | exact superpose b0e11 b0e115399
        | (have j0 := b0e115399 X0 X1
           grind)
        | exact resolve b0e115399 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e115399
      have b0e123241 : ∀ X0 X1 X2 : G, (τ X0) = X2 ∨ (σ (k X2 X1)) = (σ (M.op X2 X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1272 X2 X1
           have i₂ := b0e115569 X1 X0
           grind)
        | exact superpose b0e115569 b0e1272
        | (have j0 := b0e1272 X2 X1
           have j1 := b0e115569 X1 X0
           grind)
        | exact resolve b0e1272 b0e115569
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e115569
      have b0e123671 : (σ (M.op y x)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b0e133
           have i₂ := b0e115624 x y
           grind)
        | exact superpose b0e115624 b0e133
        | (have j1 := b0e115624 x y
           grind)
        | exact resolve b0e133 b0e115624
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e115624
      have b0e123779 : y = (M.op x x) := by
        first
        | (have j1 := b0e1272 y x
           grind)
        | (have r₁ := b0e123671
           have r₂ := b0e1272 y x
           grind)
        | exact resolve b0e123671 b0e1272
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1272 b0e123671
      have b0e124000 : ∀ X0 X1 : G, (k X0 X1) = (k y X1) ∨ (M.op X0 x) = (k X0 x) := by
        intro X0 X1
        first
        | (have i₁ := b0e92125 X0 X1 x
           have i₂ := b0e123779
           grind)
        | exact superpose b0e123779 b0e92125
        | (have j0 := b0e92125 X0 X1 x
           grind)
        | exact resolve b0e92125 b0e123779
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e92125
      have b0e125754 : ∀ X0 : G, y ≠ (k X0 y) ∨ y = (M.op y y) ∨ (M.op X0 x) = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b0e1166 y
           have i₂ := b0e124000 X0 y
           grind)
        | (have i₁ := b0e1166 x
           have i₂ := b0e124000 x x
           grind)
        | exact superpose b0e124000 b0e1166
        | (have j0 := b0e1166 y
           have j1 := b0e124000 X0 x
           grind)
        | exact resolve b0e1166 b0e124000
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1166 b0e124000
      have b0e126018 : ∀ X0 : G, y ≠ (k X0 y) ∨ x = y ∨ (M.op X0 x) = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b0e125754 X0
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e125754
        | (have j0 := b0e125754 X0
           grind)
        | exact resolve b0e125754 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e125754
      have b0e129683 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ x = y ∨ (M.op X0 x) = (k X0 x) ∨ y = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b0e126018 X0
           have i₂ := b0e41 X0 y
           grind)
        | exact superpose b0e41 b0e126018
        | (have j0 := b0e126018 X0
           have j1 := b0e41 X0 x
           grind)
        | (have r₁ := b0e126018 X0
           have r₂ := b0e41 X0 y
           grind)
        | exact resolve b0e126018 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e129787 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ x = y ∨ (M.op X0 x) = (k X0 x) := by
        intro X0
        first
        | (have j0 := b0e129683 X0
           have j1 := b0e126018 X0
           grind)
        | (have r₁ := b0e129683 X0
           have r₂ := b0e126018 X0
           grind)
        | exact resolve b0e129683 b0e126018
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e126018 b0e129683
      have b0e130639 : ∀ X0 : G, (σ (M.op y x)) ≠ (σ (k y x)) ∨ (τ X0) = y ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e133
           have i₂ := b0e3086 X0 x y
           grind)
        | exact superpose b0e3086 b0e133
        | (have j1 := b0e3086 X0 x y
           grind)
        | exact resolve b0e133 b0e3086
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3086
      have b0e130646 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (τ X0) = y := by
        intro X0
        first
        | (have j0 := b0e130639 X0
           have j1 := b0e123241 X0 x y
           grind)
        | (have r₁ := b0e130639 X0
           have r₂ := b0e123241 X0 x y
           grind)
        | exact resolve b0e130639 b0e123241
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e123241 b0e130639
      have b0e130693 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k X0 x)) ∨ (τ (σ X0)) = y := by
        intro X0
        first
        | (have i₁ := b0e15 X0 x
           have i₂ := b0e130646 (σ X0)
           grind)
        | exact superpose b0e130646 b0e15
        | (have j1 := b0e130646 (σ X0)
           grind)
        | exact resolve b0e15 b0e130646
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e130646
      have b0e130735 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k X0 x)) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e130693 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e130693
        | (have j0 := b0e130693 X0
           grind)
        | exact resolve b0e130693 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e130693
      have b0e130911 : ∀ X0 : G, (τ (σ (k x x))) = X0 ∨ (k X0 (τ (σ x))) = (M.op X0 (τ (σ x))) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b0e115069 (σ x) X0
           have i₂ := b0e130735 x
           grind)
        | exact superpose b0e130735 b0e115069
        | (have j0 := b0e115069 (σ x) X0
           have j1 := b0e130735 x
           grind)
        | exact resolve b0e115069 b0e130735
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e115069 b0e130735
      have b0e130943 : ∀ X0 : G, (k x x) = X0 ∨ (k X0 (τ (σ x))) = (M.op X0 (τ (σ x))) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b0e130911 X0
           have i₂ := b0e11 (k x x)
           grind)
        | exact superpose b0e11 b0e130911
        | (have j0 := b0e130911 X0
           grind)
        | exact resolve b0e130911 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e130911
      have b0e130997 : ∀ X0 : G, (M.op x x) = X0 ∨ (k X0 (τ (σ x))) = (M.op X0 (τ (σ x))) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b0e130943 X0
           have i₂ := b0e114467 x
           grind)
        | exact superpose b0e114467 b0e130943
        | (have j0 := b0e130943 X0
           grind)
        | exact resolve b0e130943 b0e114467
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e114467 b0e130943
      have b0e131025 : ∀ X0 : G, y = X0 ∨ (k X0 (τ (σ x))) = (M.op X0 (τ (σ x))) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b0e130997 X0
           have i₂ := b0e123779
           grind)
        | exact superpose b0e123779 b0e130997
        | (have j0 := b0e130997 X0
           grind)
        | exact resolve b0e130997 b0e123779
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e130997
      have b0e131035 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ y = X0 ∨ x = y := by
        intro X0
        first
        | (have i₁ := b0e131025 X0
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e131025
        | (have j0 := b0e131025 X0
           grind)
        | exact resolve b0e131025 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e131025
      have b0e132237 : y ≠ (M.op y x) ∨ x = y ∨ (M.op (M.op y x) x) = (k (M.op y x) x) := by
        first
        | (have i₁ := b0e129787 (M.op y x)
           have i₂ := b0e35
           grind)
        | exact superpose b0e35 b0e129787
        | (have j0 := b0e129787 (M.op y x)
           grind)
        | exact resolve b0e129787 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e129787
      have b0e132255 : x = y ∨ (M.op (M.op y x) x) = (k (M.op y x) x) := by
        first
        | (have j1 := b0e131035 (M.op y x)
           grind)
        | (have r₁ := b0e132237
           have r₂ := b0e131035 (M.op y x)
           grind)
        | exact resolve b0e132237 b0e131035
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e131035 b0e132237
      have b0e132259 : (M.op x (M.op x x)) = (k (M.op y x) x) ∨ x = y := by
        first
        | (have i₁ := b0e132255
           have i₂ := b0e10 x y
           grind)
        | exact superpose b0e10 b0e132255
        | exact resolve b0e132255 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e132255
      have b0e132260 : (M.op x y) = (k (M.op y x) x) ∨ x = y := by
        first
        | (have i₁ := b0e132259
           have i₂ := b0e123779
           grind)
        | exact superpose b0e123779 b0e132259
        | exact resolve b0e132259 b0e123779
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e132259
      have b0e132261 : (M.op y x) = (k (M.op y x) x) ∨ x = y := by
        first
        | (have i₁ := b0e132260
           have i₂ := b0e33
           grind)
        | exact superpose b0e33 b0e132260
        | exact resolve b0e132260 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e132260
      have b0e132306 : (M.op y x) = (M.op x x) ∨ (M.op (M.op y x) y) = (k (M.op y x) y) ∨ x = y := by
        first
        | (have i₁ := b0e114705 (M.op y x)
           have i₂ := b0e132261
           grind)
        | exact superpose b0e132261 b0e114705
        | (have j0 := b0e114705 (M.op y x)
           grind)
        | exact resolve b0e114705 b0e132261
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e114705 b0e132261
      have b0e132383 : y = (M.op y x) ∨ (M.op (M.op y x) y) = (k (M.op y x) y) ∨ x = y := by
        first
        | (have i₁ := b0e132306
           have i₂ := b0e123779
           grind)
        | exact superpose b0e123779 b0e132306
        | exact resolve b0e132306 b0e123779
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e123779 b0e132306
      have b0e132440 : y = (M.op y x) ∨ (M.op (M.op y x) y) = (k (M.op y x) y) := by
        first
        | (have j1 := b0e56615 (M.op y x)
           grind)
        | (have r₁ := b0e132383
           have r₂ := b0e56615 x
           grind)
        | exact resolve b0e132383 b0e56615
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56615 b0e132383
      have b0e132463 : (M.op y x) = (k (M.op y x) y) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b0e132440
           have i₂ := b0e35
           grind)
        | exact superpose b0e35 b0e132440
        | exact resolve b0e132440 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e132440
      have b0e132467 : (M.op y x) = (k (M.op y x) y) := by
        first
        | (have r₁ := b0e132463
           have r₂ := b0e111307
           grind)
        | exact resolve b0e132463 b0e111307
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e111307 b0e132463
      have b0e132520 : (M.op (σ y) (σ x)) = (σ (k (M.op y x) y)) ∨ x = (M.op y x) ∨ (σ x) = (σ (M.op y x)) := by
        first
        | (have i₁ := b0e3347 (M.op y x)
           have i₂ := b0e132467
           grind)
        | exact superpose b0e132467 b0e3347
        | (have j0 := b0e3347 (M.op y x)
           grind)
        | exact resolve b0e3347 b0e132467
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3347
      have b0e132585 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op y x) ∨ (σ x) = (σ (M.op y x)) := by
        first
        | (have i₁ := b0e132520
           have i₂ := b0e132467
           grind)
        | exact superpose b0e132467 b0e132520
        | exact resolve b0e132520 b0e132467
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e132520
      have b0e132588 : (σ x) = (σ (M.op y x)) ∨ x = (M.op y x) := by
        first
        | (have r₁ := b0e132585
           have r₂ := b0e133
           grind)
        | exact resolve b0e132585 b0e133
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e132585
      have b0e132610 : (M.op y x) = (τ (σ x)) ∨ x = (M.op y x) := by
        first
        | (have i₁ := b0e11 (M.op y x)
           have i₂ := b0e132588
           grind)
        | exact superpose b0e132588 b0e11
        | exact resolve b0e11 b0e132588
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e132588
      have b0e132699 : x = (M.op y x) ∨ x = (M.op y x) := by
        first
        | (have i₁ := b0e132610
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e132610
        | exact resolve b0e132610 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e132610
      have b0e132700 : x = (M.op y x) := by grind
      clear b0e132699
      have b0e132750 : x = (k x y) := by
        first
        | (have i₁ := b0e132467
           have i₂ := b0e132700
           grind)
        | exact superpose b0e132700 b0e132467
        | exact resolve b0e132467 b0e132700
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e132467 b0e132700
      have b0e132819 : x = y := by
        first
        | (have i₁ := b0e132750
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e132750
        | exact resolve b0e132750 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20 b0e132750
      have b0e132855 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e133
           have i₂ := b0e132819
           grind)
        | exact superpose b0e132819 b0e133
        | exact resolve b0e133 b0e132819
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e133 b0e132819
      have b0e133027 : False := by grind
      exact b0e133027
    · have b1e10 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X0) := by
        intro X0 X1
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b1e17 : x = (M.op y y) := by grind
      have b1e18 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e20 : y = (k x y) := by grind
      have b1e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 (τ X0) X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e15
        | exact resolve b1e15 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k (τ X0) X1)
           have i₂ := b1e21 X0 X1
           grind)
        | exact superpose b1e21 b1e11
        | exact resolve b1e11 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21
      have b1e28 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b1e10 y y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e36 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b1e38 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e18
           have i₂ := b1e14 X0 (σ y)
           grind)
        | (have i₁ := b1e18
           have i₂ := b1e14 (M.op (σ y) (σ y)) x
           grind)
        | exact superpose b1e14 b1e18
        | (have j1 := b1e14 X0 (σ y)
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e14 (σ x) (σ y)
           grind)
        | exact resolve b1e18 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X0 X1
           have i₂ := b1e14 (σ X0) (σ X1)
           grind)
        | exact superpose b1e14 b1e15
        | (have j1 := b1e14 (σ X0) (σ X1)
           grind)
        | exact resolve b1e15 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e59 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
        intro X0
        grind
      clear b1e26
      have b1e65 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b1e59 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e59
        | exact resolve b1e59 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e59
      have b1e125 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b1e36 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e36
      have b1e165 : x ≠ y ∨ y = (k y y) := by
        first
        | (have i₁ := b1e125 y y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e125
        | (have j0 := b1e125 y y
           grind)
        | exact resolve b1e125 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e125
      have b1e166 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b1e38 (σ x)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38
      have b1e167 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e166
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e166
        | exact resolve b1e166 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e166
      have b1e168 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e167
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e167
        | exact resolve b1e167 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e167
      have b1e169 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e168
           grind)
        | exact superpose b1e168 b1e16
        | exact resolve b1e16 b1e168
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e168
      have b1e176 : (σ y) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b1e169
           have i₂ := b1e28
           grind)
        | exact superpose b1e28 b1e169
        | exact resolve b1e169 b1e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28 b1e169
      have b1e312 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e39 y y
           grind)
        | exact superpose b1e39 b1e18
        | (have j1 := b1e39 y y
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e39 x y
           grind)
        | exact resolve b1e18 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e39
      have b1e833 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e312
           have i₂ := b1e14 y y
           grind)
        | exact superpose b1e14 b1e312
        | (have j1 := b1e14 (σ y) (σ y)
           grind)
        | exact resolve b1e312 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e312
      have b1e834 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e833
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e833
        | exact resolve b1e833 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e833
      have b1e835 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
      clear b1e834
      have b1e846 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
        first
        | (have i₁ := b1e835
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e835
        | exact resolve b1e835 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e835
      have b1e852 : y = (k (τ (σ y)) y) ∨ x = y := by
        first
        | (have i₁ := b1e65 y
           have i₂ := b1e846
           grind)
        | exact superpose b1e846 b1e65
        | exact resolve b1e65 b1e846
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e65 b1e846
      have b1e870 : y = (k y y) ∨ x = y := by
        first
        | (have i₁ := b1e852
           have i₂ := b1e11 y
           grind)
        | exact superpose b1e11 b1e852
        | exact resolve b1e852 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e852
      have b1e871 : y = (k y y) := by
        first
        | (have r₁ := b1e870
           have r₂ := b1e165
           grind)
        | exact resolve b1e870 b1e165
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e165 b1e870
      have b1e890 : y = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e14 y y
           have i₂ := b1e871
           grind)
        | exact superpose b1e871 b1e14
        | (have j0 := b1e14 y y
           grind)
        | exact resolve b1e14 b1e871
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e871
      have b1e891 : y = (M.op y y) := by grind
      clear b1e890
      have b1e914 : x = y := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e891
           grind)
        | exact superpose b1e891 b1e17
        | exact resolve b1e17 b1e891
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e891
      have b1e1050 : (σ y) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b1e176
           have i₂ := b1e914
           grind)
        | exact superpose b1e914 b1e176
        | exact resolve b1e176 b1e914
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e176
      have b1e1054 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e1050
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1050
        | exact resolve b1e1050 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1050
      have b1e1057 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e1054
           have i₂ := b1e914
           grind)
        | exact superpose b1e914 b1e1054
        | exact resolve b1e1054 b1e914
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e914 b1e1054
      have b1e1058 : False := by grind
      exact b1e1058
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X0) := by
        intro X0 X1
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b2e17 : x ≠ (M.op y y) := by grind
      have b2e18 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e20 : (σ y) = (k (σ x) (σ y)) := by grind
      have b2e21 : (σ y) = (σ (k x y)) := by
        first
        | (have i₁ := b2e20
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e20
        | exact resolve b2e20 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e20
      have b2e32 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e10 (σ y) (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e43 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b2e46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X0 X1
           have i₂ := b2e14 (σ X0) (σ X1)
           grind)
        | exact superpose b2e14 b2e15
        | (have j1 := b2e14 (σ X0) (σ X1)
           grind)
        | exact resolve b2e15 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e49 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b2e21
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e21
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e21 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21
      have b2e50 : (σ (M.op x y)) = (σ y) := by
        first
        | (have r₁ := b2e49
           have r₂ := b2e17
           grind)
        | exact resolve b2e49 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e49
      have b2e101 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e32
           grind)
        | exact superpose b2e32 b2e16
        | exact resolve b2e16 b2e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e32
      have b2e108 : (σ y) ≠ (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e101
           have i₂ := b2e50
           grind)
        | exact superpose b2e50 b2e101
        | exact resolve b2e101 b2e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50 b2e101
      have b2e403 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e46 y y
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e46
        | exact resolve b2e46 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46
      have b2e490 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e11 (k y y)
           have i₂ := b2e403
           grind)
        | exact superpose b2e403 b2e11
        | exact resolve b2e11 b2e403
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e403
      have b2e503 : x = (k y y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e490
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e490
        | exact resolve b2e490 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e490
      have b2e566 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e43 y y
           have i₂ := b2e503
           grind)
        | exact superpose b2e503 b2e43
        | exact resolve b2e43 b2e503
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e43 b2e503
      have b2e569 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b2e566
           have r₂ := b2e17
           grind)
        | exact resolve b2e566 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e566
      have b2e592 : x = (τ (σ y)) ∨ x = y := by
        first
        | (have i₁ := b2e11 x
           have i₂ := b2e569
           grind)
        | exact superpose b2e569 b2e11
        | exact resolve b2e11 b2e569
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e569
      have b2e608 : x = y ∨ x = y := by
        first
        | (have i₁ := b2e592
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e592
        | exact resolve b2e592 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e592
      have b2e609 : x = y := by grind
      clear b2e608
      have b2e684 : (σ y) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b2e108
           have i₂ := b2e609
           grind)
        | exact superpose b2e609 b2e108
        | exact resolve b2e108 b2e609
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e108
      have b2e685 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e684
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e684
        | exact resolve b2e684 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e684
      have b2e688 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b2e685
           have i₂ := b2e609
           grind)
        | exact superpose b2e609 b2e685
        | exact resolve b2e685 b2e609
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e609 b2e685
      have b2e689 : False := by grind
      exact b2e689
    · have b3e14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : x ≠ (M.op y y) := by grind
      have b3e18 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e33 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e14 X0 (σ y)
           grind)
        | (have i₁ := b3e18
           have i₂ := b3e14 (M.op (σ y) (σ y)) x
           grind)
        | exact superpose b3e14 b3e18
        | (have j1 := b3e14 X0 (σ y)
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e14 (σ x) (σ y)
           grind)
        | exact resolve b3e18 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e129 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b3e33 (σ x)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e33
      have b3e130 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e129
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e129
        | exact resolve b3e129 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e129
      have b3e147 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e130
           grind)
        | exact superpose b3e130 b3e16
        | exact resolve b3e16 b3e130
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e130
      have b3e196 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e147
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e147
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e147 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e147
      have b3e197 : x = (M.op y y) := by grind
      clear b3e196
      have b3e200 : False := by grind
      exact b3e200

/-- `Equation4401`: `x ◇ (x ◇ y) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pyx_Equation4401 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4401 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4401.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op x y) := by grind
      have b0e18 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e19 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e16
        | exact resolve b0e16 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e20 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e19
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e19
        | exact resolve b0e19 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19
      have b0e21 : False := by grind
      exact b0e21
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X0) := by
        intro X0 X1 X2
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e17 : y = (M.op x y) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e20 : y ≠ y ∨ x = (k x y) := by
        first
        | (have i₁ := b1e13 x y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e13
        | (have j0 := b1e13 x y
           grind)
        | (have r₁ := b1e13 x y
           have r₂ := b1e17
           grind)
        | exact resolve b1e13 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e21 : x = (k x y) := by grind
      clear b1e20
      have b1e22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 (τ X0) X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e15
        | exact resolve b1e15 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e15
        | exact resolve b1e15 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e24 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b1e10 X0 (M.op X0 x) X3
           have i₂ := b1e10 X0 x X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e26 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
        intro X0 X1 X3
        first
        | (have i₁ := b1e10 X0 x X3
           have i₂ := b1e10 X0 x X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e27 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y x) := by
        intro X0
        first
        | (have i₁ := b1e10 x X0 y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e30 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 X0 X1 x
           have i₂ := b1e10 X0 X2 x
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e33 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b1e27 y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e27
        | exact resolve b1e27 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e34 : (M.op y x) = (M.op x (M.op y x)) := by
        first
        | (have i₁ := b1e27 (M.op x x)
           have i₂ := b1e27 x
           grind)
        | exact superpose b1e27 b1e27
        | exact resolve b1e27 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e37 : ∀ X1 : G, (M.op y x) = (M.op (M.op x X1) x) := by
        intro X1
        first
        | (have i₁ := b1e10 x x X1
           have i₂ := b1e27 x
           grind)
        | exact superpose b1e27 b1e10
        | exact resolve b1e10 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e39 : ∀ X1 : G, (M.op x (M.op y x)) = (M.op (M.op x X1) x) := by
        intro X1
        first
        | (have i₁ := b1e10 x (M.op x x) X1
           have i₂ := b1e27 x
           grind)
        | exact superpose b1e27 b1e10
        | exact resolve b1e10 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e43 : y = (M.op y x) := by
        first
        | (have i₁ := b1e33
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e33
        | exact resolve b1e33 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e33
      have b1e46 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X1 X0
           have i₂ := b1e14 (σ X1) (σ X0)
           grind)
        | exact superpose b1e14 b1e15
        | (have j1 := b1e14 (σ X1) (σ X0)
           grind)
        | exact resolve b1e15 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e51 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e22 X1 X0
           have i₂ := b1e14 (τ X1) X0
           grind)
        | exact superpose b1e14 b1e22
        | (have j1 := b1e14 (τ X1) X0
           grind)
        | exact resolve b1e22 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e54 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k (τ X0) X1)
           have i₂ := b1e22 X0 X1
           grind)
        | exact superpose b1e22 b1e11
        | exact resolve b1e11 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e61 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k X0 (τ X1))
           have i₂ := b1e23 X1 X0
           grind)
        | exact superpose b1e23 b1e11
        | exact resolve b1e11 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e242 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) ≠ (M.op (M.op X0 X1) X0) ∨ (k X0 (M.op (M.op X0 X2) X0)) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e13 X0 (M.op (M.op X0 X2) X0)
           have i₂ := b1e24 X0 X2 X1
           grind)
        | exact superpose b1e24 b1e13
        | (have j0 := b1e13 X0 (M.op (M.op X0 X2) X0)
           grind)
        | (have r₁ := b1e13 X0 (M.op (M.op X0 x) X0)
           have r₂ := b1e24 X0 x x
           grind)
        | exact resolve b1e13 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e24
      have b1e251 : ∀ X0 X2 : G, (k X0 (M.op (M.op X0 X2) X0)) = X0 := by
        intro X0 X2
        first
        | (have j0 := b1e242 X0 x X2
           grind)
        | (have r₁ := b1e242 X0 x x
           have r₂ := b1e26 X0 x x
           grind)
        | (have r₁ := b1e242 X0 x x
           have r₂ := b1e26 X0 x x
           grind)
        | exact resolve b1e242 b1e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e242
      have b1e279 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e251 X0 x
           have i₂ := b1e10 X0 X1 x
           grind)
        | exact superpose b1e10 b1e251
        | exact resolve b1e251 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e251
      have b1e519 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e46 X0 X1
           have i₂ := b1e46 X1 X0
           grind)
        | exact superpose b1e46 b1e46
        | (have j0 := b1e46 X0 X1
           have j1 := b1e46 X0 X1
           grind)
        | exact resolve b1e46 b1e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e523 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 (σ X1) (σ X0)
           have i₂ := b1e46 X1 X0
           grind)
        | exact superpose b1e46 b1e13
        | (have j0 := b1e13 (σ X1) (σ X0)
           have j1 := b1e46 X1 X0
           grind)
        | (have r₁ := b1e13 (σ X1) (σ X0)
           have r₂ := b1e46 X0 X1
           grind)
        | exact resolve b1e13 b1e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e536 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e46 y x
           grind)
        | exact superpose b1e46 b1e18
        | (have j1 := b1e46 y x
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e46 y x
           grind)
        | exact resolve b1e18 b1e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e539 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 (σ X1) (σ X0)
           have i₂ := b1e46 X0 X1
           grind)
        | exact superpose b1e46 b1e13
        | (have j0 := b1e13 (σ X1) (σ X0)
           have j1 := b1e46 X0 X1
           grind)
        | (have r₁ := b1e13 (σ X1) (σ X0)
           have r₂ := b1e46 X0 X1
           grind)
        | exact resolve b1e13 b1e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e552 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b1e46 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e46
      have b1e553 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e539 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e539
      have b1e554 : (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
      clear b1e536
      have b1e556 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e553 X0 X1
           have i₂ := b1e15 X1 X0
           grind)
        | exact superpose b1e15 b1e553
        | (have j0 := b1e553 X0 X1
           grind)
        | exact resolve b1e553 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e553
      have b1e557 : (σ x) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e554
           have i₂ := b1e21
           grind)
        | exact superpose b1e21 b1e554
        | exact resolve b1e554 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21 b1e554
      have b1e559 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e523 X0 X1
           have i₂ := b1e15 X1 X0
           grind)
        | exact superpose b1e15 b1e523
        | (have j0 := b1e523 X0 X1
           grind)
        | exact resolve b1e523 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e523
      have b1e564 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op (σ y) X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e10 (σ y) (σ x) X0
           have i₂ := b1e557
           grind)
        | exact superpose b1e557 b1e10
        | exact resolve b1e10 b1e557
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e572 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b1e30 (σ y) X0 (σ x)
           have i₂ := b1e557
           grind)
        | exact superpose b1e557 b1e30
        | exact resolve b1e30 b1e557
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30
      have b1e578 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b1e572 X0
           have i₂ := b1e557
           grind)
        | exact superpose b1e557 b1e572
        | exact resolve b1e572 b1e557
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e572
      have b1e582 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e564 X0
           have i₂ := b1e557
           grind)
        | exact superpose b1e557 b1e564
        | exact resolve b1e564 b1e557
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e564
      have b1e880 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e54 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e54
        | exact resolve b1e54 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54
      have b1e1126 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e582 (M.op (σ y) x)
           have i₂ := b1e578 x
           grind)
        | exact superpose b1e578 b1e582
        | exact resolve b1e582 b1e578
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e578 b1e582
      have b1e1329 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e1126
           grind)
        | exact superpose b1e1126 b1e18
        | exact resolve b1e18 b1e1126
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1339 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ x) (σ x)) := by
        intro X0
        first
        | (have i₁ := b1e26 (σ x) X0 (σ y)
           have i₂ := b1e1126
           grind)
        | exact superpose b1e1126 b1e26
        | exact resolve b1e26 b1e1126
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e26
      have b1e1349 : (σ x) = (k (σ x) (M.op (σ x) (σ x))) := by
        first
        | (have i₁ := b1e279 (σ x) (σ y)
           have i₂ := b1e1126
           grind)
        | exact superpose b1e1126 b1e279
        | exact resolve b1e279 b1e1126
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e279 b1e1126
      have b1e3306 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
        first
        | (have i₁ := b1e61 x (M.op (σ x) (σ x))
           have i₂ := b1e1349
           grind)
        | exact superpose b1e1349 b1e61
        | exact resolve b1e61 b1e1349
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1349
      have b1e3308 : x = (k x (τ (M.op (σ x) (σ x)))) := by
        first
        | (have i₁ := b1e3306
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e3306
        | exact resolve b1e3306 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3306
      have b1e3890 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b1e552 (τ X0)
           have i₂ := b1e22 X0 (τ X0)
           grind)
        | exact superpose b1e22 b1e552
        | (have j0 := b1e552 (τ X0)
           grind)
        | exact resolve b1e552 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e552
      have b1e3893 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b1e3890 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e3890
        | (have j0 := b1e3890 X0
           grind)
        | exact resolve b1e3890 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3890
      have b1e3898 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b1e3893 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e3893
        | (have j0 := b1e3893 X0
           grind)
        | exact resolve b1e3893 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3893
      have b1e3907 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
        intro X0
        first
        | (have i₁ := b1e3898 (τ X0)
           have i₂ := b1e880 X0 X0
           grind)
        | exact superpose b1e880 b1e3898
        | (have j0 := b1e3898 (τ X0)
           grind)
        | exact resolve b1e3898 b1e880
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3898
      have b1e3909 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e51 X0 (σ X0)
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e51
        | exact resolve b1e51 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e51
      have b1e3951 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e3909 X0 X1
           have i₂ := b1e15 X0 X1
           grind)
        | exact superpose b1e15 b1e3909
        | (have j0 := b1e3909 X0 X1
           grind)
        | exact resolve b1e3909 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3909
      have b1e6369 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e556 X0 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e556
        | exact resolve b1e556 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e556
      have b1e6460 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e6369 X0 X1
           have i₂ := b1e22 X0 X1
           grind)
        | exact superpose b1e22 b1e6369
        | (have j0 := b1e6369 X0 X1
           grind)
        | exact resolve b1e6369 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6369
      have b1e6468 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e6460 X0 X1
           have i₂ := b1e22 X0 X1
           grind)
        | exact superpose b1e22 b1e6460
        | (have j0 := b1e6460 X0 X1
           grind)
        | exact resolve b1e6460 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6460
      have b1e16424 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e6468 X0 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e6468
        | exact resolve b1e6468 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6468
      have b1e17220 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e16424 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16424
      have b1e23090 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e559 (τ X0) (τ X1)
           have i₂ := b1e880 X1 X0
           grind)
        | exact superpose b1e880 b1e559
        | (have j0 := b1e559 (τ X0) (τ X1)
           grind)
        | exact resolve b1e559 b1e880
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e559
      have b1e23135 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e23090 X0 X1
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e23090
        | (have j0 := b1e23090 X0 X1
           grind)
        | exact resolve b1e23090 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23090
      have b1e23147 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e23135 X0 X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e23135
        | (have j0 := b1e23135 X0 X1
           grind)
        | exact resolve b1e23135 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23135
      have b1e23155 : ∀ X0 X1 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e23147 X0 X1
           have i₂ := b1e23 X0 (τ X1)
           grind)
        | exact superpose b1e23 b1e23147
        | (have j0 := b1e23147 X0 X1
           grind)
        | exact resolve b1e23147 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23147
      have b1e23158 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e23155 X0 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e23155
        | (have j0 := b1e23155 X0 X1
           grind)
        | exact resolve b1e23155 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23155
      have b1e23159 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e23158 X0 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e23158
        | (have j0 := b1e23158 X0 X1
           grind)
        | exact resolve b1e23158 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23158
      have b1e23160 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e23159 X0 X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e23159
        | (have j0 := b1e23159 X0 X1
           grind)
        | exact resolve b1e23159 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23159
      have b1e23161 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b1e23160 X0 X1
           have j1 := b1e17220 X1 X0
           grind)
        | (have r₁ := b1e23160 X1 X0
           have r₂ := b1e17220 X0 X1
           grind)
        | (have r₁ := b1e23160 X0 X1
           have r₂ := b1e17220 X0 X1
           grind)
        | exact resolve b1e23160 b1e17220
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17220 b1e23160
      have b1e23184 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (k (τ X1) (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e23161 (τ X0) (τ X1)
           have i₂ := b1e880 X1 X0
           grind)
        | exact superpose b1e880 b1e23161
        | (have j0 := b1e23161 (τ X0) (τ X1)
           grind)
        | exact resolve b1e23161 b1e880
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23161
      have b1e23215 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e23184 X0 X1
           have i₂ := b1e880 X0 X1
           grind)
        | exact superpose b1e880 b1e23184
        | (have j0 := b1e23184 X0 X1
           grind)
        | exact resolve b1e23184 b1e880
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e880 b1e23184
      have b1e53245 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e519 (τ X0) X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e519
        | exact resolve b1e519 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e519
      have b1e53519 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e53245 X0 X1
           have i₂ := b1e23 X0 X1
           grind)
        | exact superpose b1e23 b1e53245
        | (have j0 := b1e53245 X0 X1
           grind)
        | exact resolve b1e53245 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23 b1e53245
      have b1e53538 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e53519 X0 X1
           have i₂ := b1e22 X0 X1
           grind)
        | exact superpose b1e22 b1e53519
        | (have j0 := b1e53519 X0 X1
           grind)
        | exact resolve b1e53519 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22 b1e53519
      have b1e53544 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b1e53538 X0 X1
           have j1 := b1e13 X0 (σ X1)
           grind)
        | (have r₁ := b1e53538 X0 X1
           have r₂ := b1e13 X0 (σ X1)
           grind)
        | exact resolve b1e53538 b1e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53538
      have b1e53568 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e53544 X0 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e53544
        | exact resolve b1e53544 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e53606 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e61 X0 (σ X1)
           have i₂ := b1e53544 (σ X0) X1
           grind)
        | exact superpose b1e53544 b1e61
        | (have j1 := b1e53544 (σ X0) X1
           grind)
        | exact resolve b1e61 b1e53544
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e61 b1e53544
      have b1e53683 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e53606 X0 X1
           have i₂ := b1e11 X1
           grind)
        | exact superpose b1e11 b1e53606
        | (have j0 := b1e53606 X0 X1
           grind)
        | exact resolve b1e53606 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53606
      have b1e53708 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e53683 X0 X1
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e53683
        | (have j0 := b1e53683 X0 X1
           grind)
        | exact resolve b1e53683 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53683
      have b1e53716 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e53708 X0 X1
           have i₂ := b1e15 X1 X0
           grind)
        | exact superpose b1e15 b1e53708
        | (have j0 := b1e53708 X0 X1
           grind)
        | exact resolve b1e53708 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53708
      have b1e54426 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X1) = (τ (k X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e23215 X0 X1
           have i₂ := b1e53568 X1 X0
           grind)
        | exact superpose b1e53568 b1e23215
        | (have j0 := b1e23215 X0 X1
           have j1 := b1e53568 X1 X0
           grind)
        | exact resolve b1e23215 b1e53568
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23215 b1e53568
      have b1e54465 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b1e54426 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54426
      have b1e58968 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (M.op X0 X0) := by
        intro X0
        first
        | (have i₁ := b1e3907 X0
           have i₂ := b1e54465 X0 X0
           grind)
        | exact superpose b1e54465 b1e3907
        | (have j0 := b1e3907 X0
           have j1 := b1e54465 X0 X0
           grind)
        | (have r₁ := b1e3907 X0
           have r₂ := b1e54465 X0 X0
           grind)
        | exact resolve b1e3907 b1e54465
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3907 b1e54465
      have b1e58992 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (M.op X0 X0) := by
        intro X0
        first
        | (have j0 := b1e58968 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e58968
      have b1e60630 : x = (k x (τ (σ (k x x)))) ∨ x = (k x x) := by
        first
        | (have i₁ := b1e3308
           have i₂ := b1e53716 x x
           grind)
        | exact superpose b1e53716 b1e3308
        | (have j1 := b1e53716 x (τ (σ (k x x)))
           grind)
        | exact resolve b1e3308 b1e53716
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3308 b1e53716
      have b1e60833 : x = (k x (k x x)) ∨ x = (k x x) := by
        first
        | (have i₁ := b1e60630
           have i₂ := b1e11 (k x x)
           grind)
        | exact superpose b1e11 b1e60630
        | exact resolve b1e60630 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e60630
      have b1e61016 : x = (k x (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e60833
           have i₂ := b1e14 x x
           grind)
        | exact superpose b1e14 b1e60833
        | (have j1 := b1e14 x x
           grind)
        | exact resolve b1e60833 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e60833
      have b1e61034 : x = (k x (M.op x x)) ∨ x = (M.op x x) := by grind
      clear b1e61016
      have b1e62396 : (σ x) = (σ (M.op (M.op x x) x)) ∨ (M.op x x) = (M.op x (M.op x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e3951 x (M.op x x)
           have i₂ := b1e61034
           grind)
        | exact superpose b1e61034 b1e3951
        | (have j0 := b1e3951 x (M.op x x)
           grind)
        | exact resolve b1e3951 b1e61034
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e61034
      have b1e62404 : (σ x) = (σ (M.op x (M.op y x))) ∨ (M.op x x) = (M.op x (M.op x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e62396
           have i₂ := b1e39 x
           grind)
        | exact superpose b1e39 b1e62396
        | exact resolve b1e62396 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e39 b1e62396
      have b1e62407 : (σ x) = (σ (M.op y x)) ∨ (M.op x x) = (M.op x (M.op x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e62404
           have i₂ := b1e34
           grind)
        | exact superpose b1e34 b1e62404
        | exact resolve b1e62404 b1e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34 b1e62404
      have b1e62410 : (σ x) = (σ y) ∨ (M.op x x) = (M.op x (M.op x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e62407
           have i₂ := b1e43
           grind)
        | exact superpose b1e43 b1e62407
        | exact resolve b1e62407 b1e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e62407
      have b1e62413 : (M.op x x) = (M.op x (M.op x x)) ∨ x = (M.op x x) := by
        first
        | (have r₁ := b1e62410
           have r₂ := b1e1329
           grind)
        | exact resolve b1e62410 b1e1329
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e62410
      have b1e62416 : (M.op y x) = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e62413
           have i₂ := b1e27 x
           grind)
        | exact superpose b1e27 b1e62413
        | exact resolve b1e62413 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27 b1e62413
      have b1e62419 : x = (M.op x x) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b1e62416
           have i₂ := b1e43
           grind)
        | exact superpose b1e43 b1e62416
        | exact resolve b1e62416 b1e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e62416
      have b1e63555 : (M.op y x) = (M.op x x) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b1e37 x
           have i₂ := b1e62419
           grind)
        | exact superpose b1e62419 b1e37
        | exact resolve b1e37 b1e62419
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e37 b1e62419
      have b1e63735 : y = (M.op x x) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b1e63555
           have i₂ := b1e43
           grind)
        | exact superpose b1e43 b1e63555
        | exact resolve b1e63555 b1e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e43 b1e63555
      have b1e63736 : y = (M.op x x) := by grind
      clear b1e63735
      have b1e113760 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e58992 (σ X0)
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e58992
        | (have j0 := b1e58992 (σ X0)
           grind)
        | exact resolve b1e58992 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e58992
      have b1e113911 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b1e113760 X0
           have i₂ := b1e15 X0 X0
           grind)
        | exact superpose b1e15 b1e113760
        | (have j0 := b1e113760 X0
           grind)
        | exact resolve b1e113760 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e113760
      have b1e124771 : (σ (k x x)) = (M.op (σ (k x x)) (σ x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e1339 (σ x)
           have i₂ := b1e113911 x
           grind)
        | exact superpose b1e113911 b1e1339
        | (have j1 := b1e113911 x
           grind)
        | exact resolve b1e1339 b1e113911
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1339 b1e113911
      have b1e124879 : (σ (k x x)) = (M.op (σ (k x x)) (σ x)) ∨ x = y := by
        first
        | (have i₁ := b1e124771
           have i₂ := b1e63736
           grind)
        | exact superpose b1e63736 b1e124771
        | exact resolve b1e124771 b1e63736
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e124771
      have b1e142332 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e124879
           have i₂ := b1e3951 x x
           grind)
        | exact superpose b1e3951 b1e124879
        | (have j1 := b1e3951 x x
           grind)
        | exact resolve b1e124879 b1e3951
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3951 b1e124879
      have b1e142409 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e142332
           have i₂ := b1e63736
           grind)
        | exact superpose b1e63736 b1e142332
        | exact resolve b1e142332 b1e63736
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e142332
      have b1e142415 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e142409
           have i₂ := b1e557
           grind)
        | exact superpose b1e557 b1e142409
        | exact resolve b1e142409 b1e557
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e557 b1e142409
      have b1e142421 : x = y ∨ x = (M.op x x) := by
        first
        | (have r₁ := b1e142415
           have r₂ := b1e1329
           grind)
        | exact resolve b1e142415 b1e1329
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e142415
      have b1e142426 : x = y ∨ x = y := by
        first
        | (have i₁ := b1e142421
           have i₂ := b1e63736
           grind)
        | exact superpose b1e63736 b1e142421
        | exact resolve b1e142421 b1e63736
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e63736 b1e142421
      have b1e142427 : x = y := by grind
      clear b1e142426
      have b1e144450 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e1329
           have i₂ := b1e142427
           grind)
        | exact superpose b1e142427 b1e1329
        | exact resolve b1e1329 b1e142427
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1329 b1e142427
      have b1e144485 : False := by grind
      exact b1e144485
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X0) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b2e17 : y ≠ (M.op x y) := by grind
      have b2e18 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e19 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e16
        | exact resolve b2e16 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e20 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b2e13 (σ x) (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e13
        | (have j0 := b2e13 (σ x) (σ y)
           grind)
        | (have r₁ := b2e13 (σ x) (σ y)
           have r₂ := b2e18
           grind)
        | exact resolve b2e13 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e21 : (σ x) = (k (σ x) (σ y)) := by grind
      clear b2e20
      have b2e22 : (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b2e21
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e21
        | exact resolve b2e21 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21
      have b2e23 : (k x y) = (τ (σ x)) := by
        first
        | (have i₁ := b2e11 (k x y)
           have i₂ := b2e22
           grind)
        | exact superpose b2e22 b2e11
        | exact resolve b2e11 b2e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e22
      have b2e24 : x = (k x y) := by
        first
        | (have i₁ := b2e23
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e23
        | exact resolve b2e23 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e23
      have b2e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 (τ X0) X1
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e15
        | exact resolve b2e15 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e31 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e10 (σ x) (σ y) X0
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e32 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b2e10 X0 (M.op X0 x) X3
           have i₂ := b2e10 X0 x X1
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e34 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
        intro X0 X1 X3
        first
        | (have i₁ := b2e10 X0 x X3
           have i₂ := b2e10 X0 x X1
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e35 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e10 (σ x) X0 (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e38 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 X0 X1 x
           have i₂ := b2e10 X0 X2 x
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e41 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e31 X0
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e31
        | exact resolve b2e31 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e31
      have b2e48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X1 X0
           have i₂ := b2e14 (σ X1) (σ X0)
           grind)
        | exact superpose b2e14 b2e15
        | (have j1 := b2e14 (σ X1) (σ X0)
           grind)
        | exact resolve b2e15 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e50 : x = (M.op y x) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b2e24
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e24
        | (have j1 := b2e14 y x
           grind)
        | exact resolve b2e24 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e24
      have b2e53 : x = (M.op y x) := by
        first
        | (have r₁ := b2e50
           have r₂ := b2e17
           grind)
        | exact resolve b2e50 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50
      have b2e69 : (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e41 (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e41
        | exact resolve b2e41 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e72 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ x) X0)) := by
        intro X0
        first
        | (have i₁ := b2e10 (σ x) X0 x
           have i₂ := b2e41 x
           grind)
        | exact superpose b2e41 b2e10
        | exact resolve b2e10 b2e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e100 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) := by
        intro X0
        first
        | (have i₁ := b2e34 y X0 x
           have i₂ := b2e53
           grind)
        | exact superpose b2e53 b2e34
        | exact resolve b2e34 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e145 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b2e38 y X0 x
           have i₂ := b2e53
           grind)
        | exact superpose b2e53 b2e38
        | exact resolve b2e38 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e163 : ∀ X0 : G, x = (M.op y (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b2e145 X0
           have i₂ := b2e53
           grind)
        | exact superpose b2e53 b2e145
        | exact resolve b2e145 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e53 b2e145
      have b2e175 : ∀ X0 : G, x = (M.op y (M.op (M.op y X0) y)) := by
        intro X0
        first
        | (have i₁ := b2e163 (M.op y x)
           have i₂ := b2e10 y x X0
           grind)
        | exact superpose b2e10 b2e163
        | exact resolve b2e163 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e192 : x = (M.op y (M.op x y)) := by
        first
        | (have i₁ := b2e175 x
           have i₂ := b2e100 x
           grind)
        | exact superpose b2e100 b2e175
        | exact resolve b2e175 b2e100
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e175
      have b2e197 : ∀ X1 : G, (M.op x y) = (M.op y (M.op (M.op y X1) y)) := by
        intro X1
        first
        | (have i₁ := b2e32 y X1 (M.op y x)
           have i₂ := b2e163 x
           grind)
        | exact superpose b2e163 b2e32
        | exact resolve b2e32 b2e163
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e163
      have b2e252 : (M.op x y) = (M.op y (M.op x y)) := by
        first
        | (have i₁ := b2e197 x
           have i₂ := b2e100 x
           grind)
        | exact superpose b2e100 b2e197
        | exact resolve b2e197 b2e100
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e100 b2e197
      have b2e255 : x = (M.op x y) := by
        first
        | (have i₁ := b2e252
           have i₂ := b2e192
           grind)
        | exact superpose b2e192 b2e252
        | exact resolve b2e252 b2e192
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e192 b2e252
      have b2e256 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e19
           have i₂ := b2e255
           grind)
        | exact superpose b2e255 b2e19
        | exact resolve b2e19 b2e255
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19
      have b2e257 : x ≠ y := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e255
           grind)
        | exact superpose b2e255 b2e17
        | exact resolve b2e17 b2e255
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e262 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b2e34 x X0 y
           have i₂ := b2e255
           grind)
        | exact superpose b2e255 b2e34
        | exact resolve b2e34 b2e255
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e264 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b2e38 x X0 y
           have i₂ := b2e255
           grind)
        | exact superpose b2e255 b2e38
        | exact resolve b2e38 b2e255
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e38 b2e255
      have b2e573 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e35 (σ X0)
           have i₂ := b2e48 X0 x
           grind)
        | exact superpose b2e48 b2e35
        | (have j1 := b2e48 X0 x
           grind)
        | exact resolve b2e35 b2e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e35
      have b2e577 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e13 (σ X1) (σ X0)
           have i₂ := b2e48 X0 X1
           grind)
        | exact superpose b2e48 b2e13
        | (have j0 := b2e13 (σ X1) (σ X0)
           have j1 := b2e48 X0 X1
           grind)
        | (have r₁ := b2e13 (σ X1) (σ X0)
           have r₂ := b2e48 X0 X1
           grind)
        | exact resolve b2e13 b2e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e590 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b2e577 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e577
      have b2e592 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e590 X0 X1
           have i₂ := b2e15 X1 X0
           grind)
        | exact superpose b2e15 b2e590
        | (have j0 := b2e590 X0 X1
           grind)
        | exact resolve b2e590 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e590
      have b2e593 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ X0)) ∨ (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e573 X0
           have i₂ := b2e69
           grind)
        | exact superpose b2e69 b2e573
        | (have j0 := b2e573 X0
           grind)
        | exact resolve b2e573 b2e69
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e69 b2e573
      have b2e7328 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e592 X0 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e592
        | exact resolve b2e592 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e592
      have b2e7419 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e7328 X0 X1
           have i₂ := b2e25 X0 X1
           grind)
        | exact superpose b2e25 b2e7328
        | (have j0 := b2e7328 X0 X1
           grind)
        | exact resolve b2e7328 b2e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e7328
      have b2e7425 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e7419 X0 X1
           have i₂ := b2e25 X0 X1
           grind)
        | exact superpose b2e25 b2e7419
        | (have j0 := b2e7419 X0 X1
           grind)
        | exact resolve b2e7419 b2e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e25 b2e7419
      have b2e7790 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e7425 X0 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e7425
        | exact resolve b2e7425 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e7425
      have b2e8042 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b2e7790 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e8179 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op (M.op X0 X2) X0) = (k (M.op (M.op X0 X2) X0) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e8042 (M.op (M.op X0 X2) X0) X0
           have i₂ := b2e32 X0 X2 X1
           grind)
        | exact superpose b2e32 b2e8042
        | (have j0 := b2e8042 (M.op (M.op X0 X2) X0) X0
           grind)
        | (have r₁ := b2e8042 (M.op (M.op X0 x) X0) X0
           have r₂ := b2e32 X0 x x
           grind)
        | exact resolve b2e8042 b2e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e32 b2e8042
      have b2e8240 : ∀ X0 X2 : G, (M.op (M.op X0 X2) X0) = (k (M.op (M.op X0 X2) X0) X0) := by
        intro X0 X2
        first
        | (have j0 := b2e8179 X0 x X2
           grind)
        | (have r₁ := b2e8179 X0 x x
           have r₂ := b2e34 X0 x x
           grind)
        | (have r₁ := b2e8179 X0 x x
           have r₂ := b2e34 X0 x x
           grind)
        | exact resolve b2e8179 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34 b2e8179
      have b2e8456 : ∀ X0 : G, (σ X0) = (σ y) ∨ (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e48 X0 x
           have i₂ := b2e593 X0
           grind)
        | exact superpose b2e593 b2e48
        | (have j0 := b2e48 X0 x
           have j1 := b2e593 X0
           grind)
        | exact resolve b2e48 b2e593
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e593
      have b2e8580 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ y) := by
        intro X0
        first
        | (have j0 := b2e8456 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e8456
      have b2e8806 : (M.op x x) = (k (M.op x x) x) := by
        first
        | (have i₁ := b2e8240 x x
           have i₂ := b2e262 x
           grind)
        | exact superpose b2e262 b2e8240
        | exact resolve b2e8240 b2e262
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e262 b2e8240
      have b2e13812 : (σ y) = (M.op (σ (k x x)) (σ x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e41 (σ x)
           have i₂ := b2e8580 x
           grind)
        | exact superpose b2e8580 b2e41
        | (have j1 := b2e8580 x
           grind)
        | exact resolve b2e41 b2e8580
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e41
      have b2e13813 : (σ y) = (M.op (σ x) (σ (k x x))) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e72 (σ x)
           have i₂ := b2e8580 x
           grind)
        | exact superpose b2e8580 b2e72
        | (have j1 := b2e8580 x
           grind)
        | exact resolve b2e72 b2e8580
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e72 b2e8580
      have b2e13887 : (σ y) = (M.op (σ x) (σ (k x x))) := by
        first
        | (have r₁ := b2e13813
           have r₂ := b2e256
           grind)
        | exact resolve b2e13813 b2e256
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e13813
      have b2e13888 : (σ y) = (M.op (σ (k x x)) (σ x)) := by
        first
        | (have r₁ := b2e13812
           have r₂ := b2e256
           grind)
        | exact resolve b2e13812 b2e256
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e13812
      have b2e15571 : (σ x) = (σ y) ∨ (M.op (σ x) (σ (k x x))) = (σ (k (k x x) x)) := by
        first
        | (have i₁ := b2e48 x (k x x)
           have i₂ := b2e13888
           grind)
        | exact superpose b2e13888 b2e48
        | (have j0 := b2e48 x (k x x)
           grind)
        | exact resolve b2e48 b2e13888
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e48 b2e13888
      have b2e15686 : (M.op (σ x) (σ (k x x))) = (σ (k (k x x) x)) := by
        first
        | (have r₁ := b2e15571
           have r₂ := b2e256
           grind)
        | exact resolve b2e15571 b2e256
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e256 b2e15571
      have b2e15699 : (σ y) = (σ (k (k x x) x)) := by
        first
        | (have i₁ := b2e15686
           have i₂ := b2e13887
           grind)
        | exact superpose b2e13887 b2e15686
        | exact resolve b2e15686 b2e13887
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e13887 b2e15686
      have b2e16375 : (τ (σ y)) = (k (k x x) x) := by
        first
        | (have i₁ := b2e11 (k (k x x) x)
           have i₂ := b2e15699
           grind)
        | exact superpose b2e15699 b2e11
        | exact resolve b2e11 b2e15699
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e15699
      have b2e16425 : y = (k (k x x) x) := by
        first
        | (have i₁ := b2e16375
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e16375
        | exact resolve b2e16375 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16375
      have b2e17200 : y = (k (M.op x x) x) ∨ x = (k x x) := by
        first
        | (have i₁ := b2e16425
           have i₂ := b2e7790 x x
           grind)
        | exact superpose b2e7790 b2e16425
        | (have j1 := b2e7790 x x
           grind)
        | exact resolve b2e16425 b2e7790
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e17211 : x = (k x x) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b2e17200
           have i₂ := b2e8806
           grind)
        | exact superpose b2e8806 b2e17200
        | exact resolve b2e17200 b2e8806
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e8806 b2e17200
      have b2e18792 : y = (k x x) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b2e16425
           have i₂ := b2e17211
           grind)
        | exact superpose b2e17211 b2e16425
        | exact resolve b2e16425 b2e17211
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16425 b2e17211
      have b2e19015 : y = (M.op x x) ∨ x = y ∨ y = (M.op x x) := by
        first
        | (have i₁ := b2e7790 x x
           have i₂ := b2e18792
           grind)
        | exact superpose b2e18792 b2e7790
        | exact resolve b2e7790 b2e18792
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e7790 b2e18792
      have b2e19019 : y = (M.op x x) ∨ x = y := by grind
      clear b2e19015
      have b2e19025 : y = (M.op x x) := by
        first
        | (have r₁ := b2e19019
           have r₂ := b2e257
           grind)
        | exact resolve b2e19019 b2e257
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e257 b2e19019
      have b2e19308 : y = (M.op x y) := by
        first
        | (have i₁ := b2e264 x
           have i₂ := b2e19025
           grind)
        | exact superpose b2e19025 b2e264
        | exact resolve b2e264 b2e19025
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e264 b2e19025
      have b2e19452 : False := by grind
      exact b2e19452
    · have b3e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X0) := by
        intro X0 X1 X2
        grind
      have b3e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b3e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b3e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x y) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 (τ X0) X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e15
        | exact resolve b3e15 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e21 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b3e10 X0 (M.op X0 x) X3
           have i₂ := b3e10 X0 x X1
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e24 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (M.op (M.op (M.op X0 X1) X0) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10 X0 X2 (M.op X0 x)
           have i₂ := b3e10 X0 x X1
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e26 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10 X0 X1 x
           have i₂ := b3e10 X0 X2 x
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e34 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e14 (σ X1) (σ X0)
           grind)
        | exact superpose b3e14 b3e15
        | (have j1 := b3e14 (σ X1) (σ X0)
           grind)
        | exact resolve b3e15 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e35 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e19 X1 X0
           have i₂ := b3e14 (τ X1) X0
           grind)
        | exact superpose b3e14 b3e19
        | (have j1 := b3e14 (τ X1) X0
           grind)
        | exact resolve b3e19 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e19
      have b3e130 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op X0 (M.op (M.op (M.op X0 X1) X0) X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e21 X0 (M.op (M.op X0 x) X0) X2
           have i₂ := b3e21 X0 x X1
           grind)
        | exact superpose b3e21 b3e21
        | exact resolve b3e21 b3e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e21
      have b3e211 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (M.op X0 (M.op (M.op (M.op X0 X1) X0) X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e26 X0 X2 (M.op X0 x)
           have i₂ := b3e24 X0 X1 x
           grind)
        | exact superpose b3e24 b3e26
        | exact resolve b3e26 b3e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e24
      have b3e322 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e34 x y
           grind)
        | exact superpose b3e34 b3e16
        | (have j1 := b3e34 x y
           grind)
        | exact resolve b3e16 b3e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e323 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e34 x y
           grind)
        | exact superpose b3e34 b3e18
        | (have j1 := b3e34 x y
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e34 y x
           grind)
        | exact resolve b3e18 b3e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e325 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (σ X1) X2)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10 (σ X1) X2 (σ X0)
           have i₂ := b3e34 X1 X0
           grind)
        | exact superpose b3e34 b3e10
        | (have j1 := b3e34 X1 X0
           grind)
        | exact resolve b3e10 b3e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e334 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op (σ X1) (M.op (σ X1) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e26 (σ X1) X2 (σ X0)
           have i₂ := b3e34 X1 X0
           grind)
        | exact superpose b3e34 b3e26
        | (have j1 := b3e34 X1 X0
           grind)
        | exact resolve b3e26 b3e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e342 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e34 y x
           grind)
        | exact superpose b3e34 b3e18
        | (have j1 := b3e34 y x
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e34 y x
           grind)
        | exact resolve b3e18 b3e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e34
      have b3e362 : (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
      clear b3e342
      have b3e367 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b3e323
           have i₂ := b3e362
           grind)
        | exact superpose b3e362 b3e323
        | exact resolve b3e323 b3e362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e323
      have b3e368 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b3e322
           have i₂ := b3e362
           grind)
        | exact superpose b3e362 b3e322
        | exact resolve b3e322 b3e362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e322
      have b3e373 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (σ y) (σ (k x y))) := by
        intro X0
        first
        | (have i₁ := b3e10 (σ y) (σ x) X0
           have i₂ := b3e362
           grind)
        | exact superpose b3e362 b3e10
        | exact resolve b3e10 b3e362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e2389 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e35 X0 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e35
        | exact resolve b3e35 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e35
      have b3e2433 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e2389 X0 X1
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e2389
        | (have j0 := b3e2389 X0 X1
           grind)
        | exact resolve b3e2389 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2389
      have b3e2657 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op y x) := by
        first
        | (have i₁ := b3e368
           have i₂ := b3e2433 y x
           grind)
        | exact superpose b3e2433 b3e368
        | (have j1 := b3e2433 y x
           grind)
        | (have r₁ := b3e368
           have r₂ := b3e2433 y x
           grind)
        | exact resolve b3e368 b3e2433
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e368 b3e2433
      have b3e2658 : (σ x) = (σ (k x y)) ∨ x = (M.op y x) := by grind
      clear b3e2657
      have b3e2668 : (k x y) = (τ (σ x)) ∨ x = (M.op y x) := by
        first
        | (have i₁ := b3e11 (k x y)
           have i₂ := b3e2658
           grind)
        | exact superpose b3e2658 b3e11
        | exact resolve b3e11 b3e2658
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2658
      have b3e2702 : x = (k x y) ∨ x = (M.op y x) := by
        first
        | (have i₁ := b3e2668
           have i₂ := b3e11 x
           grind)
        | exact superpose b3e11 b3e2668
        | exact resolve b3e2668 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2668
      have b3e2770 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
        first
        | (have i₁ := b3e14 x y
           have i₂ := b3e2702
           grind)
        | exact superpose b3e2702 b3e14
        | (have j0 := b3e14 y x
           grind)
        | exact resolve b3e14 b3e2702
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2702
      have b3e2771 : x = (M.op y x) ∨ y = (M.op x y) := by grind
      clear b3e2770
      have b3e2774 : x = (M.op y x) := by
        first
        | (have r₁ := b3e2771
           have r₂ := b3e17
           grind)
        | exact resolve b3e2771 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2771
      have b3e2978 : x ≠ x ∨ y = (k y x) := by
        first
        | (have i₁ := b3e13 y x
           have i₂ := b3e2774
           grind)
        | exact superpose b3e2774 b3e13
        | (have j0 := b3e13 y x
           grind)
        | (have r₁ := b3e13 y x
           have r₂ := b3e2774
           grind)
        | exact resolve b3e13 b3e2774
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e2987 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b3e26 y X0 x
           have i₂ := b3e2774
           grind)
        | exact superpose b3e2774 b3e26
        | exact resolve b3e26 b3e2774
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e26
      have b3e3010 : y = (k y x) := by grind
      clear b3e2978
      have b3e3017 : ∀ X0 : G, x = (M.op y (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b3e2987 X0
           have i₂ := b3e2774
           grind)
        | exact superpose b3e2774 b3e2987
        | exact resolve b3e2987 b3e2774
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2774 b3e2987
      have b3e3222 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b3e367
           have i₂ := b3e3010
           grind)
        | exact superpose b3e3010 b3e367
        | exact resolve b3e367 b3e3010
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e367 b3e3010
      have b3e3225 : (σ x) = (σ (k x y)) := by grind
      clear b3e3222
      have b3e3690 : ∀ X1 : G, x = (M.op (M.op y X1) y) := by
        intro X1
        first
        | (have i₁ := b3e10 y x X1
           have i₂ := b3e3017 x
           grind)
        | exact superpose b3e3017 b3e10
        | exact resolve b3e10 b3e3017
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e4279 : x = (M.op x y) := by
        first
        | (have i₁ := b3e3690 (M.op y x)
           have i₂ := b3e3017 x
           grind)
        | exact superpose b3e3017 b3e3690
        | exact resolve b3e3690 b3e3017
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e3017 b3e3690
      have b3e23418 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        intro X0
        first
        | (have i₁ := b3e325 x y X0
           have i₂ := b3e3225
           grind)
        | exact superpose b3e3225 b3e325
        | (have j0 := b3e325 x y x
           grind)
        | exact resolve b3e325 b3e3225
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e325
      have b3e23696 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) := by
        intro X0
        first
        | (have j0 := b3e23418 X0
           grind)
        | (have r₁ := b3e23418 X0
           have r₂ := b3e18
           grind)
        | exact resolve b3e23418 b3e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e23418
      have b3e24456 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        intro X0
        first
        | (have i₁ := b3e334 x y X0
           have i₂ := b3e3225
           grind)
        | exact superpose b3e3225 b3e334
        | (have j0 := b3e334 x y x
           grind)
        | exact resolve b3e334 b3e3225
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e334
      have b3e24797 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) X0)) := by
        intro X0
        first
        | (have j0 := b3e24456 X0
           grind)
        | (have r₁ := b3e24456 X0
           have r₂ := b3e18
           grind)
        | exact resolve b3e24456 b3e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e24456
      have b3e24825 : ∀ X0 : G, (σ (k x y)) = (M.op (σ y) (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b3e24797 X0
           have i₂ := b3e362
           grind)
        | exact superpose b3e362 b3e24797
        | exact resolve b3e24797 b3e362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e24797
      have b3e24851 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b3e24825 X0
           have i₂ := b3e3225
           grind)
        | exact superpose b3e3225 b3e24825
        | exact resolve b3e24825 b3e3225
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e24825
      have b3e25045 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
        intro X0
        first
        | (have i₁ := b3e130 (σ y) (M.op (σ y) x) X0
           have i₂ := b3e24851 x
           grind)
        | exact superpose b3e24851 b3e130
        | exact resolve b3e130 b3e24851
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e130
      have b3e25084 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
        intro X0
        first
        | (have i₁ := b3e211 (σ y) (M.op (σ y) x) X0
           have i₂ := b3e24851 x
           grind)
        | exact superpose b3e24851 b3e211
        | exact resolve b3e211 b3e24851
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e211 b3e24851
      have b3e25149 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
        first
        | (have i₁ := b3e25084 x
           have i₂ := b3e23696 x
           grind)
        | exact superpose b3e23696 b3e25084
        | exact resolve b3e25084 b3e23696
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e23696 b3e25084
      have b3e25183 : (M.op (σ y) (σ (k x y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
        first
        | (have i₁ := b3e25045 x
           have i₂ := b3e373 x
           grind)
        | exact superpose b3e373 b3e25045
        | exact resolve b3e25045 b3e373
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e373 b3e25045
      have b3e25307 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (k x y))) := by
        first
        | (have i₁ := b3e25183
           have i₂ := b3e25149
           grind)
        | exact superpose b3e25149 b3e25183
        | exact resolve b3e25183 b3e25149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e25149 b3e25183
      have b3e25389 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b3e25307
           have i₂ := b3e3225
           grind)
        | exact superpose b3e3225 b3e25307
        | exact resolve b3e25307 b3e3225
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e25307
      have b3e25433 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e25389
           have i₂ := b3e362
           grind)
        | exact superpose b3e362 b3e25389
        | exact resolve b3e25389 b3e362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e362 b3e25389
      have b3e25459 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b3e25433
           have i₂ := b3e3225
           grind)
        | exact superpose b3e3225 b3e25433
        | exact resolve b3e25433 b3e3225
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e3225 b3e25433
      have b3e26900 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e25459
           grind)
        | exact superpose b3e25459 b3e16
        | exact resolve b3e16 b3e25459
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e25459
      have b3e27019 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b3e26900
           have i₂ := b3e4279
           grind)
        | exact superpose b3e4279 b3e26900
        | exact resolve b3e26900 b3e4279
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e4279 b3e26900
      have b3e27020 : False := by grind
      exact b3e27020

/-- `Equation4402`: `x ◇ (x ◇ y) = (x ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4402 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4402 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4402.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X1) := by
        intro X0 X1 X2
        grind
      have b0e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op x x) := by grind
      have b0e18 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 (τ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (k (τ X0) X1)
           have i₂ := b0e23 X0 X1
           grind)
        | exact superpose b0e23 b0e11
        | exact resolve b0e11 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X1) = (M.op (M.op X0 X2) (M.op X0 (M.op X0 X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 (M.op X0 X2) X1 X3
           have i₂ := b0e10 X0 X1 X2
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X0 X2 X3
           have i₂ := b0e10 X0 X2 X1
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X0 X3 (M.op X0 X2)
           have i₂ := b0e10 X0 X2 X1
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e10 (σ x) X0 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e10 x X0 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 (M.op X0 (M.op X0 X1)))) := by
        intro X0 X1
        grind
      have b0e43 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e39 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e39
        | exact resolve b0e39 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X0 X1 : G, (M.op x (M.op x X1)) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 x X1 (M.op x X0)
           have i₂ := b0e39 X0
           grind)
        | exact superpose b0e39 b0e10
        | exact resolve b0e10 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : ∀ X1 : G, (M.op x (M.op x X1)) = (M.op y (M.op y X1)) := by
        intro X1
        first
        | (have i₁ := b0e45 x X1
           have i₂ := b0e10 y X1 x
           grind)
        | exact superpose b0e10 b0e45
        | exact resolve b0e45 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e47 : ∀ X1 : G, (M.op y X1) = (M.op y (M.op y X1)) := by
        intro X1
        first
        | (have i₁ := b0e46 X1
           have i₂ := b0e39 X1
           grind)
        | exact superpose b0e39 b0e46
        | exact resolve b0e46 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e53 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X0 X1
           have i₂ := b0e14 (σ X0) (σ X1)
           grind)
        | exact superpose b0e14 b0e15
        | (have j1 := b0e14 (σ X0) (σ X1)
           grind)
        | exact resolve b0e15 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e65 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e24 X1 X0
           have i₂ := b0e14 X0 (τ X1)
           grind)
        | exact superpose b0e14 b0e24
        | (have j1 := b0e14 X0 (τ X1)
           grind)
        | exact resolve b0e24 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e70 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (k X0 (τ X1))
           have i₂ := b0e24 X1 X0
           grind)
        | exact superpose b0e24 b0e11
        | exact resolve b0e11 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e97 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e34 (σ x) X0 X1 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e34
        | exact resolve b0e34 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e139 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e38 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e38
        | exact resolve b0e38 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e163 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e53 (σ X1) (σ X0)
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e53
        | exact resolve b0e53 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e170 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e53 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53
      have b0e215 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      have b0e229 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e215 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e215
        | exact resolve b0e215 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e215
      have b0e256 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (σ x) X1)) = (M.op (M.op (M.op (σ y) X0) X2) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e36 (σ x) (M.op (σ x) X0) X2 X1
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e36
        | exact resolve b0e36 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e301 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) X1)) = (M.op (σ y) (M.op (σ y) X1)) := by
        intro X1
        first
        | (have i₁ := b0e256 x X1 x
           have i₂ := b0e36 (σ y) x x X1
           grind)
        | exact superpose b0e36 b0e256
        | exact resolve b0e256 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e256
      have b0e309 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ y) (M.op (σ y) X1)) := by
        intro X1
        first
        | (have i₁ := b0e301 X1
           have i₂ := b0e38 X1
           grind)
        | exact superpose b0e38 b0e301
        | exact resolve b0e301 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e301
      have b0e325 : x ≠ y ∨ x = (k x x) := by
        first
        | (have i₁ := b0e170 x x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e170
        | (have j0 := b0e170 x x
           grind)
        | exact resolve b0e170 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e559 : ∀ X0 : G, (M.op (σ y) X0) = (k (M.op (σ y) X0) (M.op (σ x) (M.op (σ x) (M.op (σ y) X0)))) := by
        intro X0
        first
        | (have i₁ := b0e41 (σ x) (M.op (σ x) X0)
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e41
        | exact resolve b0e41 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e582 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) (M.op y (M.op y X0))) := by
        intro X0
        first
        | (have i₁ := b0e41 y X0
           have i₂ := b0e47 (M.op y X0)
           grind)
        | exact superpose b0e47 b0e41
        | exact resolve b0e41 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e586 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e582 X0
           have i₂ := b0e47 X0
           grind)
        | (have i₁ := b0e582 X0
           have i₂ := b0e47 (M.op y X0)
           grind)
        | exact superpose b0e47 b0e582
        | exact resolve b0e582 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e582
      have b0e597 : ∀ X0 : G, (M.op (σ y) X0) = (k (M.op (σ y) X0) (M.op (σ y) (M.op (σ y) X0))) := by
        intro X0
        first
        | (have i₁ := b0e559 X0
           have i₂ := b0e38 (M.op (σ y) X0)
           grind)
        | exact superpose b0e38 b0e559
        | exact resolve b0e559 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e559
      have b0e608 : ∀ X0 : G, (M.op (σ y) X0) = (k (M.op (σ y) X0) (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e597 X0
           have i₂ := b0e309 X0
           grind)
        | (have i₁ := b0e597 X0
           have i₂ := b0e309 (M.op (σ y) X0)
           grind)
        | exact superpose b0e309 b0e597
        | exact resolve b0e597 b0e309
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e309 b0e597
      have b0e1461 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X1)) := by
        intro X0 X1 X2
        grind
      clear b0e32
      have b0e1480 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e1461 X0 X1 x
           have i₂ := b0e36 X0 (M.op X0 X1) x X1
           grind)
        | exact superpose b0e36 b0e1461
        | exact resolve b0e1461 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e1461
      have b0e2486 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1
           have i₂ := b0e58 X0 X1
           grind)
        | exact superpose b0e58 b0e11
        | (have j1 := b0e58 X0 X1
           grind)
        | exact resolve b0e11 b0e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2522 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e58 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58
      have b0e3699 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e608 (σ y)
           have i₂ := b0e14 (σ y) x
           grind)
        | (have i₁ := b0e608 X0
           have i₂ := b0e14 X0 (M.op (σ y) X0)
           grind)
        | exact superpose b0e14 b0e608
        | (have j1 := b0e14 (σ y) X0
           grind)
        | exact resolve b0e608 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e608
      have b0e7245 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (M.op (σ y) (σ X0)) = (k (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e70 X0 (σ X0)
           have i₂ := b0e3699 (σ X0)
           grind)
        | exact superpose b0e3699 b0e70
        | (have j1 := b0e3699 (σ X0)
           grind)
        | exact resolve b0e70 b0e3699
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70 b0e3699
      have b0e7265 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ y) (σ X0)) = (k (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e7245 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e7245
        | (have j0 := b0e7245 X0
           grind)
        | exact resolve b0e7245 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7245
      have b0e7278 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e7265 X0
           have i₂ := b0e15 y X0
           grind)
        | exact superpose b0e15 b0e7265
        | (have j0 := b0e7265 X0
           grind)
        | exact resolve b0e7265 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7265
      have b0e12427 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e65 X0 (σ X0)
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e65
        | exact resolve b0e65 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65
      have b0e12594 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e12427 X0 X1
           have i₂ := b0e15 X1 X0
           grind)
        | exact superpose b0e15 b0e12427
        | (have j0 := b0e12427 X0 X1
           grind)
        | exact resolve b0e12427 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12427
      have b0e19914 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e163 x x
           grind)
        | exact superpose b0e163 b0e18
        | (have j1 := b0e163 x x
           grind)
        | exact resolve b0e18 b0e163
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e163
      have b0e20030 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ (k x x)) := by
        first
        | (have i₁ := b0e11 (k x x)
           have i₂ := b0e19914
           grind)
        | exact superpose b0e19914 b0e11
        | exact resolve b0e11 b0e19914
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19914
      have b0e20063 : (σ x) = (σ (k x x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e20030
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e20030
        | exact resolve b0e20030 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20030
      have b0e54704 : ∀ X0 : G, (τ (σ y)) = X0 ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e2486 x X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e2486
        | (have j0 := b0e2486 x X0
           grind)
        | exact resolve b0e2486 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e54803 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (σ (k x X0)) X1) ∨ (τ (M.op (σ x) (σ x))) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e97 (σ X0) X1
           have i₂ := b0e2486 x X0
           grind)
        | exact superpose b0e2486 b0e97
        | (have j1 := b0e2486 x X0
           grind)
        | exact resolve b0e97 b0e2486
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e97 b0e2486
      have b0e54928 : ∀ X0 X1 : G, (τ (σ y)) = X0 ∨ (M.op (σ y) X1) = (M.op (σ (k x X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e54803 X0 X1
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e54803
        | (have j0 := b0e54803 X0 X1
           grind)
        | exact resolve b0e54803 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54803
      have b0e54950 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e54704 X0
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e54704
        | (have j0 := b0e54704 X0
           grind)
        | exact resolve b0e54704 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54704
      have b0e54962 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (σ (k x X0)) X1) ∨ y = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e54928 X0 X1
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e54928
        | (have j0 := b0e54928 X0 X1
           grind)
        | exact resolve b0e54928 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54928
      have b0e55945 : ∀ X0 : G, (M.op (σ x) X0) = (σ (k x (τ X0))) ∨ (τ X0) = y := by
        intro X0
        first
        | (have i₁ := b0e54950 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e54950
        | (have j0 := b0e54950 (τ X0)
           grind)
        | exact resolve b0e54950 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55978 : x = (k x (τ (σ (k x x)))) ∨ x = y := by
        first
        | (have i₁ := b0e229 x
           have i₂ := b0e54950 x
           grind)
        | exact superpose b0e54950 b0e229
        | (have j1 := b0e54950 x
           grind)
        | exact resolve b0e229 b0e54950
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e229 b0e54950
      have b0e56156 : x = (k x (k x x)) ∨ x = y := by
        first
        | (have i₁ := b0e55978
           have i₂ := b0e11 (k x x)
           grind)
        | exact superpose b0e11 b0e55978
        | exact resolve b0e55978 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55978
      have b0e56164 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ (τ X0) = y := by
        intro X0
        first
        | (have i₁ := b0e55945 X0
           have i₂ := b0e24 X0 x
           grind)
        | exact superpose b0e24 b0e55945
        | (have j0 := b0e55945 X0
           grind)
        | exact resolve b0e55945 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24 b0e55945
      have b0e60162 : ∀ X0 : G, (k (τ (σ x)) X0) = (τ (M.op (σ x) (σ X0))) ∨ (τ (σ X0)) = y := by
        intro X0
        first
        | (have i₁ := b0e29 (σ x) X0
           have i₂ := b0e56164 (σ X0)
           grind)
        | exact superpose b0e56164 b0e29
        | (have j1 := b0e56164 (σ X0)
           grind)
        | exact resolve b0e29 b0e56164
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29 b0e56164
      have b0e60188 : ∀ X0 : G, (k x X0) = (τ (M.op (σ x) (σ X0))) ∨ (τ (σ X0)) = y := by
        intro X0
        first
        | (have i₁ := b0e60162 X0
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e60162
        | (have j0 := b0e60162 X0
           grind)
        | exact resolve b0e60162 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60162
      have b0e60220 : ∀ X0 : G, (k x X0) = (τ (M.op (σ x) (σ X0))) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e60188 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e60188
        | (have j0 := b0e60188 X0
           grind)
        | exact resolve b0e60188 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60188
      have b0e62588 : (τ (M.op (σ x) (σ x))) = (k x (k x x)) ∨ y = (k x x) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e60220 (k x x)
           have i₂ := b0e20063
           grind)
        | exact superpose b0e20063 b0e60220
        | (have j0 := b0e60220 (k x x)
           grind)
        | exact resolve b0e60220 b0e20063
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20063 b0e60220
      have b0e62630 : (τ (M.op (σ x) (σ x))) = (k x (k x x)) ∨ y = (k x x) := by grind
      clear b0e62588
      have b0e62638 : (τ (σ y)) = (k x (k x x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e62630
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e62630
        | exact resolve b0e62630 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62630
      have b0e62644 : y = (k x (k x x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e62638
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e62638
        | exact resolve b0e62638 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62638
      have b0e65255 : y = (M.op x (k x x)) ∨ (M.op x x) = (k x x) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e14 x (k x x)
           have i₂ := b0e62644
           grind)
        | exact superpose b0e62644 b0e14
        | (have j0 := b0e14 x (k x x)
           grind)
        | exact resolve b0e14 b0e62644
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e65263 : (σ y) = (σ (M.op x (k x x))) ∨ (M.op x x) = (k x x) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e12594 (k x x) x
           have i₂ := b0e62644
           grind)
        | exact superpose b0e62644 b0e12594
        | (have j0 := b0e12594 (k x x) x
           grind)
        | exact resolve b0e12594 b0e62644
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62644
      have b0e65271 : y = (k x x) ∨ (σ y) = (σ (M.op x (k x x))) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e65263
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e65263
        | exact resolve b0e65263 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65263
      have b0e65272 : (σ y) = (σ (M.op x (k x x))) ∨ y = (k x x) := by grind
      clear b0e65271
      have b0e65277 : y = (k x x) ∨ y = (M.op x (k x x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e65255
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e65255
        | exact resolve b0e65255 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65255
      have b0e65278 : y = (M.op x (k x x)) ∨ y = (k x x) := by grind
      clear b0e65277
      have b0e68107 : (M.op x y) = (M.op y (k x x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e39 (k x x)
           have i₂ := b0e65278
           grind)
        | exact superpose b0e65278 b0e39
        | exact resolve b0e39 b0e65278
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e68142 : x ≠ y ∨ x = (k x (k x x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e170 x (k x x)
           have i₂ := b0e65278
           grind)
        | exact superpose b0e65278 b0e170
        | (have j0 := b0e170 x (k x x)
           grind)
        | exact resolve b0e170 b0e65278
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e170 b0e65278
      have b0e68258 : x = (k x (k x x)) ∨ y = (k x x) := by
        first
        | (have r₁ := b0e68142
           have r₂ := b0e56156
           grind)
        | exact resolve b0e68142 b0e56156
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56156 b0e68142
      have b0e71028 : x = (M.op x (k x x)) ∨ (M.op x x) = (k x x) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e14 x (k x x)
           have i₂ := b0e68258
           grind)
        | exact superpose b0e68258 b0e14
        | (have j0 := b0e14 x (k x x)
           grind)
        | exact resolve b0e14 b0e68258
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e71047 : y = (k x x) ∨ x = (M.op x (k x x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e71028
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e71028
        | exact resolve b0e71028 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71028
      have b0e71048 : x = (M.op x (k x x)) ∨ y = (k x x) := by grind
      clear b0e71047
      have b0e73740 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) ∨ y = (k x x) := by
        intro X0
        first
        | (have i₁ := b0e10 x X0 (k x x)
           have i₂ := b0e71048
           grind)
        | exact superpose b0e71048 b0e10
        | exact resolve b0e10 b0e71048
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e73821 : (M.op x x) = (k (M.op x x) (M.op x x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e1480 x (k x x)
           have i₂ := b0e71048
           grind)
        | exact superpose b0e71048 b0e1480
        | exact resolve b0e1480 b0e71048
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1480 b0e71048
      have b0e73845 : y = (k y y) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e73821
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e73821
        | exact resolve b0e73821 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e73821
      have b0e73895 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ y = (k x x) := by
        intro X0
        first
        | (have i₁ := b0e73740 X0
           have i₂ := b0e39 X0
           grind)
        | exact superpose b0e39 b0e73740
        | exact resolve b0e73740 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e73740
      have b0e76984 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e2522 y
           have i₂ := b0e73845
           grind)
        | exact superpose b0e73845 b0e2522
        | (have j0 := b0e2522 y
           grind)
        | exact resolve b0e2522 b0e73845
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2522 b0e73845
      have b0e76994 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x x) := by grind
      clear b0e76984
      have b0e95271 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ y = (k x x) ∨ y = (k x x) := by
        intro X0
        first
        | (have i₁ := b0e54962 (k x x) X0
           have i₂ := b0e68258
           grind)
        | exact superpose b0e68258 b0e54962
        | (have j0 := b0e54962 (k x x) x
           grind)
        | exact resolve b0e54962 b0e68258
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54962 b0e68258
      have b0e95573 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ y = (k x x) := by
        intro X0
        first
        | (have j0 := b0e95271 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e95271
      have b0e140865 : (M.op x y) = (M.op x (k x x)) ∨ y = (k x x) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e73895 (k x x)
           have i₂ := b0e68107
           grind)
        | exact superpose b0e68107 b0e73895
        | exact resolve b0e73895 b0e68107
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68107 b0e73895
      have b0e141005 : (M.op x y) = (M.op x (k x x)) ∨ y = (k x x) := by grind
      clear b0e140865
      have b0e146611 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e76994
           have i₂ := b0e95573 (σ y)
           grind)
        | exact superpose b0e95573 b0e76994
        | exact resolve b0e76994 b0e95573
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76994 b0e95573
      have b0e146872 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by grind
      clear b0e146611
      have b0e150866 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e146872
           grind)
        | exact superpose b0e146872 b0e16
        | exact resolve b0e16 b0e146872
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e146872
      have b0e170955 : (σ (M.op x y)) = (σ y) ∨ y = (k x x) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e65272
           have i₂ := b0e141005
           grind)
        | exact superpose b0e141005 b0e65272
        | exact resolve b0e65272 b0e141005
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65272 b0e141005
      have b0e171111 : (σ (M.op x y)) = (σ y) ∨ y = (k x x) := by grind
      clear b0e170955
      have b0e171129 : y = (k x x) := by
        first
        | (have r₁ := b0e171111
           have r₂ := b0e150866
           grind)
        | exact resolve b0e171111 b0e150866
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e150866 b0e171111
      have b0e227901 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (k x x) := by
        first
        | (have i₁ := b0e139
           have i₂ := b0e7278 x
           grind)
        | exact superpose b0e7278 b0e139
        | (have j1 := b0e7278 x
           grind)
        | exact resolve b0e139 b0e7278
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e139 b0e7278
      have b0e228027 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = y := by
        first
        | (have i₁ := b0e227901
           have i₂ := b0e171129
           grind)
        | exact superpose b0e171129 b0e227901
        | exact resolve b0e227901 b0e171129
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e227901
      have b0e230513 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e228027
           grind)
        | exact superpose b0e228027 b0e16
        | exact resolve b0e16 b0e228027
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e228027
      have b0e233035 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y ∨ x = (M.op y y) := by
        first
        | (have i₁ := b0e230513
           have i₂ := b0e12594 x y
           grind)
        | exact superpose b0e12594 b0e230513
        | (have j1 := b0e12594 x y
           grind)
        | exact resolve b0e230513 b0e12594
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12594 b0e230513
      have b0e233037 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op y y) := by
        first
        | (have i₁ := b0e233035
           have i₂ := b0e43
           grind)
        | exact superpose b0e43 b0e233035
        | exact resolve b0e233035 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e233035
      have b0e233038 : x = (M.op y y) ∨ x = y := by grind
      clear b0e233037
      have b0e235286 : x = (k x x) ∨ x = y := by
        first
        | (have i₁ := b0e586 y
           have i₂ := b0e233038
           grind)
        | exact superpose b0e233038 b0e586
        | exact resolve b0e586 b0e233038
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e586 b0e233038
      have b0e235684 : x = (k x x) := by
        first
        | (have r₁ := b0e235286
           have r₂ := b0e325
           grind)
        | exact resolve b0e235286 b0e325
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e325 b0e235286
      have b0e238495 : x = y := by
        first
        | (have i₁ := b0e171129
           have i₂ := b0e235684
           grind)
        | exact superpose b0e235684 b0e171129
        | exact resolve b0e171129 b0e235684
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e171129 b0e235684
      have b0e240892 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e238495
           grind)
        | exact superpose b0e238495 b0e16
        | exact resolve b0e16 b0e238495
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e238495
      have b0e240994 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e240892
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e240892
        | exact resolve b0e240892 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e240892
      have b0e241014 : False := by grind
      exact b0e241014
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X1) := by
        intro X0 X1 X2
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e17 : y = (M.op x x) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e20 : x = (k x y) := by grind
      have b1e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X1) = (M.op (M.op X0 X2) (M.op X0 (M.op X0 X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 (M.op X0 X2) X1 X3
           have i₂ := b1e10 X0 X1 X2
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X0 X2 X3
           have i₂ := b1e10 X0 X2 X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e34 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X0 X3 (M.op X0 X2)
           have i₂ := b1e10 X0 X2 X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e48 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e52 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b1e18
           have i₂ := b1e14 (σ x) X0
           grind)
        | (have i₁ := b1e18
           have i₂ := b1e14 X0 (M.op (σ x) (σ x))
           grind)
        | exact superpose b1e14 b1e18
        | (have j1 := b1e14 (σ x) X0
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e14 (σ x) (σ y)
           grind)
        | exact resolve b1e18 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e138 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e48 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e48
      have b1e235 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b1e52 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e52
      have b1e236 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e235
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e235
        | exact resolve b1e235 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e235
      have b1e237 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e236
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e236
        | exact resolve b1e236 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e236
      have b1e241 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e31 (σ x) (σ y) X0 X1
           have i₂ := b1e237
           grind)
        | exact superpose b1e237 b1e31
        | exact resolve b1e31 b1e237
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e31
      have b1e242 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
        intro X0
        first
        | (have i₁ := b1e10 (σ x) X0 (σ y)
           have i₂ := b1e237
           grind)
        | exact superpose b1e237 b1e10
        | exact resolve b1e10 b1e237
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e939 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) X0) X1) (σ y)) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ x))) := by
        intro X0 X1
        first
        | (have i₁ := b1e30 (σ x) (σ y) X0 X1
           have i₂ := b1e237
           grind)
        | exact superpose b1e237 b1e30
        | exact resolve b1e30 b1e237
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30
      have b1e1077 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) X0) X1) (σ y)) = (M.op (σ x) (M.op (σ x) (σ x))) := by
        intro X0 X1
        first
        | (have i₁ := b1e939 X0 X1
           have i₂ := b1e241 (M.op (σ x) (σ x)) X0
           grind)
        | exact superpose b1e241 b1e939
        | exact resolve b1e939 b1e241
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e241 b1e939
      have b1e1142 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) X0) X1) (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e1077 X0 X1
           have i₂ := b1e242 (σ x)
           grind)
        | exact superpose b1e242 b1e1077
        | exact resolve b1e1077 b1e242
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1077
      have b1e1169 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
        first
        | (have i₁ := b1e1142 x x
           have i₂ := b1e34 (σ x) x x (σ y)
           grind)
        | exact superpose b1e34 b1e1142
        | exact resolve b1e1142 b1e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34 b1e1142
      have b1e1184 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b1e1169
           have i₂ := b1e242 (σ y)
           grind)
        | exact superpose b1e242 b1e1169
        | exact resolve b1e1169 b1e242
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e242 b1e1169
      have b1e1190 : (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b1e1184
           have i₂ := b1e237
           grind)
        | exact superpose b1e237 b1e1184
        | exact resolve b1e1184 b1e237
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e237 b1e1184
      have b1e1198 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e1190
           grind)
        | exact superpose b1e1190 b1e18
        | exact resolve b1e18 b1e1190
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1214 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
        first
        | (have i₁ := b1e138 (σ x) (σ x)
           have i₂ := b1e1190
           grind)
        | exact superpose b1e1190 b1e138
        | (have j0 := b1e138 (σ x) (σ x)
           grind)
        | (have r₁ := b1e138 (σ x) (σ x)
           have r₂ := b1e1190
           grind)
        | exact resolve b1e138 b1e1190
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e138 b1e1190
      have b1e1215 : (σ x) = (k (σ x) (σ x)) := by grind
      clear b1e1214
      have b1e1216 : (σ x) = (σ (k x x)) := by
        first
        | (have i₁ := b1e1215
           have i₂ := b1e15 x x
           grind)
        | exact superpose b1e15 b1e1215
        | exact resolve b1e1215 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1215
      have b1e1614 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e1216
           have i₂ := b1e14 x x
           grind)
        | exact superpose b1e14 b1e1216
        | (have j1 := b1e14 x x
           grind)
        | exact resolve b1e1216 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1216
      have b1e1625 : (σ x) = (σ y) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e1614
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1614
        | exact resolve b1e1614 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1614
      have b1e1629 : x = (M.op x x) := by
        first
        | (have r₁ := b1e1625
           have r₂ := b1e1198
           grind)
        | exact resolve b1e1625 b1e1198
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1625
      have b1e2027 : x = y := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e1629
           grind)
        | exact superpose b1e1629 b1e17
        | exact resolve b1e17 b1e1629
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1629
      have b1e2252 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b1e1198
           have i₂ := b1e2027
           grind)
        | exact superpose b1e2027 b1e1198
        | exact resolve b1e1198 b1e2027
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1198 b1e2027
      have b1e2253 : False := by grind
      exact b1e2253
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X1) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e17 : y ≠ (M.op x x) := by grind
      have b2e18 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e20 : (σ x) = (k (σ x) (σ y)) := by grind
      have b2e21 : (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b2e20
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e20
        | exact resolve b2e20 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e20
      have b2e22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 (τ X0) X1
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e15
        | exact resolve b2e15 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e26 : (k x y) = (τ (σ x)) := by
        first
        | (have i₁ := b2e11 (k x y)
           have i₂ := b2e21
           grind)
        | exact superpose b2e21 b2e11
        | exact resolve b2e11 b2e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21
      have b2e27 : x = (k x y) := by
        first
        | (have i₁ := b2e26
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e26
        | exact resolve b2e26 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e26
      have b2e42 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
        intro X0
        grind
      clear b2e22
      have b2e46 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b2e42 X0
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e42
        | exact resolve b2e42 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e42
      have b2e56 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ y) = X0 := by
        intro X0
        first
        | (have i₁ := b2e18
           have i₂ := b2e14 (σ x) X0
           grind)
        | (have i₁ := b2e18
           have i₂ := b2e14 X0 (M.op (σ x) (σ x))
           grind)
        | exact superpose b2e14 b2e18
        | (have j1 := b2e14 (σ x) X0
           grind)
        | exact resolve b2e18 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e59 : x = (M.op x y) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b2e27
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e27
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e27 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27
      have b2e62 : x = (M.op x y) := by
        first
        | (have r₁ := b2e59
           have r₂ := b2e17
           grind)
        | exact resolve b2e59 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e59
      have b2e64 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b2e10 x X0 y
           have i₂ := b2e62
           grind)
        | exact superpose b2e62 b2e10
        | exact resolve b2e10 b2e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e119 : x = (M.op x x) := by
        first
        | (have i₁ := b2e64 y
           have i₂ := b2e62
           grind)
        | exact superpose b2e62 b2e64
        | exact resolve b2e64 b2e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e62 b2e64
      have b2e139 : x ≠ y := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e119
           grind)
        | exact superpose b2e119 b2e17
        | exact resolve b2e17 b2e119
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e289 : (σ x) = (M.op (σ x) (σ (M.op (τ (σ x)) (τ (σ x))))) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
        first
        | (have i₁ := b2e56 (σ (M.op (τ (σ x)) (τ (σ x))))
           have i₂ := b2e46 (σ x)
           grind)
        | exact superpose b2e46 b2e56
        | (have j0 := b2e56 (σ (M.op (τ (σ x)) (τ (σ x))))
           grind)
        | exact resolve b2e56 b2e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46 b2e56
      have b2e292 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
        first
        | (have i₁ := b2e289
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e289
        | exact resolve b2e289 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e289
      have b2e298 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
        first
        | (have i₁ := b2e292
           have i₂ := b2e119
           grind)
        | exact superpose b2e119 b2e292
        | exact resolve b2e292 b2e119
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e292
      have b2e301 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
        first
        | (have i₁ := b2e298
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e298
        | exact resolve b2e298 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e298
      have b2e303 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e301
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e301
        | exact resolve b2e301 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e301
      have b2e305 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e303
           have i₂ := b2e119
           grind)
        | exact superpose b2e119 b2e303
        | exact resolve b2e303 b2e119
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e119 b2e303
      have b2e306 : (σ x) = (σ y) := by grind
      clear b2e305
      have b2e459 : y = (τ (σ x)) := by
        first
        | (have i₁ := b2e11 y
           have i₂ := b2e306
           grind)
        | exact superpose b2e306 b2e11
        | exact resolve b2e11 b2e306
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e306
      have b2e460 : x = y := by
        first
        | (have i₁ := b2e459
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e459
        | exact resolve b2e459 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e459
      have b2e465 : False := by grind
      exact b2e465
    · have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x x) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e44 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e14 (σ x) X0
           grind)
        | (have i₁ := b3e18
           have i₂ := b3e14 X0 (M.op (σ x) (σ x))
           grind)
        | exact superpose b3e14 b3e18
        | (have j1 := b3e14 (σ x) X0
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e14 (σ x) (σ y)
           grind)
        | exact resolve b3e18 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e202 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b3e44 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e44
      have b3e203 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e202
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e202
        | exact resolve b3e202 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e202
      have b3e291 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e203
           grind)
        | exact superpose b3e203 b3e16
        | exact resolve b3e16 b3e203
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e203
      have b3e340 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b3e291
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e291
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e291 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e291
      have b3e341 : y = (M.op x x) := by grind
      clear b3e340
      have b3e343 : False := by grind
      exact b3e343
