import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4441`: `x ◇ (y ◇ x) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pxy_Equation4441 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4441 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4441.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e18 : y = (M.op y y) := by grind
        have b0e19 : (σ y) = (M.op (σ y) (σ y)) := by grind
        have b0e20 : x = (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b0e33 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e11 (σ y) (σ y) X0 X1
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e11
          | exact resolve b0e11 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e39 : ∀ X0 X1 : G, (M.op x (M.op X0 x)) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e11 x X0 x X1
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e11
          | exact resolve b0e11 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e40 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e11 y X0 y X1
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e11
          | exact resolve b0e11 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e41 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e11 X0 X1 x x
             have i₂ := b0e11 X0 X2 x x
             grind)
          | exact superpose b0e11 b0e11
          | exact resolve b0e11 b0e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e44 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e33 X0 X1
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e33
          | exact resolve b0e33 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e33
        have b0e47 : ∀ X0 X2 : G, (M.op x X0) = (M.op x X2) := by
          intro X0 X2
          first
          | (have i₁ := b0e39 x X2
             have i₂ := b0e39 x X0
             grind)
          | (have i₁ := b0e39 X0 x
             have i₂ := b0e39 X0 (M.op X0 x)
             grind)
          | exact superpose b0e39 b0e39
          | exact resolve b0e39 b0e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e39
        have b0e64 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e14 X1 X0
             have i₂ := b0e15 X2 X0
             grind)
          | exact superpose b0e15 b0e14
          | (have j0 := b0e14 X1 X0
             have j1 := b0e15 X2 X0
             grind)
          | (have r₁ := b0e14 X0 X1
             have r₂ := b0e15 X0 X1
             grind)
          | exact resolve b0e14 b0e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e16 X0 X1
             have i₂ := b0e15 (σ X0) (σ X1)
             grind)
          | exact superpose b0e15 b0e16
          | (have j1 := b0e15 X0 (σ X1)
             grind)
          | exact resolve b0e16 b0e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e72 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b0e64 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e64
        have b0e93 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b0e20
             have i₂ := b0e47 x X0
             grind)
          | (have i₁ := b0e20
             have i₂ := b0e47 X0 x
             grind)
          | exact superpose b0e47 b0e20
          | exact resolve b0e20 b0e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e47
        have b0e105 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
          intro X0 X2
          first
          | (have i₁ := b0e40 x X2
             have i₂ := b0e40 x X0
             grind)
          | (have i₁ := b0e40 X0 x
             have i₂ := b0e40 X0 (M.op X0 y)
             grind)
          | exact superpose b0e40 b0e40
          | exact resolve b0e40 b0e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e40
        have b0e128 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 x) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e11 X0 x X1 X2
             have i₂ := b0e93 X0
             grind)
          | exact superpose b0e93 b0e11
          | exact resolve b0e11 b0e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e145 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X0 (σ y)) := by
          intro X0 X2 X3
          first
          | (have i₁ := b0e11 X0 (M.op (σ y) x) X2 X3
             have i₂ := b0e44 x X0
             grind)
          | exact superpose b0e44 b0e11
          | exact resolve b0e11 b0e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e44
        have b0e150 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b0e145 X0 x x
             have i₂ := b0e128 X0 x x
             grind)
          | exact superpose b0e128 b0e145
          | exact resolve b0e145 b0e128
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e145
        have b0e176 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b0e18
             have i₂ := b0e105 y X0
             grind)
          | (have i₁ := b0e18
             have i₂ := b0e105 X0 y
             grind)
          | exact superpose b0e105 b0e18
          | exact resolve b0e18 b0e105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e181 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X1 (M.op y X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b0e11 X1 y X2 X3
             have i₂ := b0e105 X1 X0
             grind)
          | (have i₁ := b0e11 X1 y X2 X3
             have i₂ := b0e105 X0 X1
             grind)
          | exact superpose b0e105 b0e11
          | exact resolve b0e11 b0e105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e105
        have b0e185 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X1 (M.op y X0)) := by
          intro X0 X1
          first
          | (have i₁ := b0e181 X0 X1 x x
             have i₂ := b0e128 X1 x x
             grind)
          | exact superpose b0e128 b0e181
          | exact resolve b0e181 b0e128
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e128 b0e181
        have b0e187 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b0e185 x X1
             have i₂ := b0e176 x
             grind)
          | exact superpose b0e176 b0e185
          | exact resolve b0e185 b0e176
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e185
        have b0e431 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b0e41 X0 X1 y
             have i₂ := b0e176 X0
             grind)
          | exact superpose b0e176 b0e41
          | exact resolve b0e41 b0e176
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41 b0e176
        have b0e667 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b0e72 X1 X0 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e72
        have b0e1390 : (σ (M.op x y)) ≠ (M.op (σ x) x) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e150 (σ x)
             grind)
          | exact superpose b0e150 b0e17
          | exact resolve b0e17 b0e150
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e150
        have b0e1399 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b0e1390
             have i₂ := b0e187 (σ x)
             grind)
          | exact superpose b0e187 b0e1390
          | exact resolve b0e1390 b0e187
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e187 b0e1390
        have b0e1404 : (σ x) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b0e1399
             have i₂ := b0e93 y
             grind)
          | exact superpose b0e93 b0e1399
          | exact resolve b0e1399 b0e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e1399
        have b0e3317 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b0e71 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e71
        have b0e5260 : ∀ X0 : G, x ≠ x ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b0e667 x X0
             have i₂ := b0e93 X0
             grind)
          | exact superpose b0e93 b0e667
          | (have j0 := b0e667 x X0
             grind)
          | (have r₁ := b0e667 x X0
             have r₂ := b0e93 X0
             grind)
          | exact resolve b0e667 b0e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e93 b0e667
        have b0e5273 : ∀ X0 : G, x = (k x X0) := by
          intro X0
          first
          | (have j0 := b0e5260 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e5260
        have b0e8059 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e3317 x
             have i₂ := b0e5273 x
             grind)
          | exact superpose b0e5273 b0e3317
          | (have j0 := b0e3317 x
             grind)
          | exact resolve b0e3317 b0e5273
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e3317 b0e5273
        have b0e8064 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b0e8059
        have b0e8135 : (M.op (σ x) (σ x)) = (M.op (σ x) y) := by
          first
          | (have i₁ := b0e431 (σ x) (σ x)
             have i₂ := b0e8064
             grind)
          | exact superpose b0e8064 b0e431
          | exact resolve b0e431 b0e8064
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e431
        have b0e8139 : (σ x) = (M.op (σ x) y) := by
          first
          | (have i₁ := b0e8135
             have i₂ := b0e8064
             grind)
          | exact superpose b0e8064 b0e8135
          | exact resolve b0e8135 b0e8064
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e8064 b0e8135
        have b0e8158 : False := by grind
        exact b0e8158
      · have b1e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b1e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e18 : y = (M.op y y) := by grind
        have b1e19 : (σ y) = (M.op (σ y) (σ y)) := by grind
        have b1e20 : x ≠ (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
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
        have b1e39 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 (σ y) (σ y) X0 X1
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e11
          | exact resolve b1e11 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e45 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 y X0 y X1
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e11
          | exact resolve b1e11 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e46 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e11 X0 X1 x x
             have i₂ := b1e11 X0 X2 x x
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e49 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e39 X0 X1
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e39
          | exact resolve b1e39 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e59 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e14 X1 X0
             have i₂ := b1e15 X2 X0
             grind)
          | exact superpose b1e15 b1e14
          | (have j0 := b1e14 X1 X0
             have j1 := b1e15 X2 X0
             grind)
          | (have r₁ := b1e14 X0 X1
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e14 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e60 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 X2) ∨ (M.op X3 X0) = (k X3 X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11 X0 X1 X0 X2
             have i₂ := b1e15 X3 X0
             grind)
          | exact superpose b1e15 b1e11
          | (have j1 := b1e15 X3 X0
             grind)
          | exact resolve b1e11 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e61 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X2) ∨ (M.op X3 X0) = (k X3 X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11 X0 X0 X1 X2
             have i₂ := b1e15 X3 X0
             grind)
          | exact superpose b1e15 b1e11
          | (have j1 := b1e15 X3 X0
             grind)
          | exact resolve b1e11 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e68 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e59 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e77 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
          intro X0 X2
          first
          | (have i₁ := b1e45 x X2
             have i₂ := b1e45 x X0
             grind)
          | (have i₁ := b1e45 X0 x
             have i₂ := b1e45 X0 (M.op X0 y)
             grind)
          | exact superpose b1e45 b1e45
          | exact resolve b1e45 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e109 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e18
             have i₂ := b1e77 y X0
             grind)
          | (have i₁ := b1e18
             have i₂ := b1e77 X0 y
             grind)
          | exact superpose b1e77 b1e18
          | exact resolve b1e18 b1e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e77
        have b1e117 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e49 (σ y) X0
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e49
          | exact resolve b1e49 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e127 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X0 (σ y)) := by
          intro X0 X2 X3
          first
          | (have i₁ := b1e11 X0 (M.op (σ y) x) X2 X3
             have i₂ := b1e49 x X0
             grind)
          | exact superpose b1e49 b1e11
          | exact resolve b1e11 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e158 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (k X0 (τ X1))
             have i₂ := b1e26 X1 X0
             grind)
          | exact superpose b1e26 b1e12
          | exact resolve b1e12 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e371 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e46 X0 X1 (σ y)
             have i₂ := b1e117 X0
             grind)
          | exact superpose b1e117 b1e46
          | exact resolve b1e46 b1e117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e117
        have b1e375 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e46 X0 X1 y
             have i₂ := b1e109 X0
             grind)
          | exact superpose b1e109 b1e46
          | exact resolve b1e46 b1e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46 b1e109
        have b1e436 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e371 X0 x
             have i₂ := b1e375 X0 x
             grind)
          | exact superpose b1e375 b1e371
          | exact resolve b1e371 b1e375
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e371 b1e375
        have b1e491 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e17
             have i₂ := b1e436 (σ x)
             grind)
          | exact superpose b1e436 b1e17
          | exact resolve b1e17 b1e436
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e644 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e68 X1 X0 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e1657 : ∀ X0 X1 X3 X4 X5 : G, (M.op X0 X1) = (M.op X0 X3) ∨ (M.op X4 X0) = (k X4 X0) ∨ (M.op X5 X0) = (k X5 X0) := by
          intro X0 X1 X3 X4 X5
          first
          | (have i₁ := b1e60 X0 x X3 X4
             have i₂ := b1e60 X0 x X1 X5
             grind)
          | (have i₁ := b1e60 X0 X1 x X3
             have i₂ := b1e60 X0 X1 (M.op X1 X0) X3
             grind)
          | exact superpose b1e60 b1e60
          | (have j0 := b1e60 X0 X1 x X4
             have j1 := b1e60 X0 X1 x X4
             grind)
          | exact resolve b1e60 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e2010 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = X0 ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X3 X0) = (k X3 X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e61 X1 X1 X2 X3
             have i₂ := b1e15 X0 X1
             grind)
          | exact superpose b1e15 b1e61
          | (have j0 := b1e61 X0 X1 X2 X2
             have j1 := b1e15 X2 X0
             grind)
          | exact resolve b1e61 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e13182 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X2) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e2010 X1 X2 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2010
        have b1e13183 : ∀ X0 X1 X2 : G, (M.op X1 X2) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e13182 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13182
        have b1e14954 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X2) = (M.op X1 X3) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1 X2 X3
          first
          | (have j0 := b1e1657 X1 X2 X3 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1657
        have b1e14955 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X1 X3) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1 X2 X3
          first
          | (have j0 := b1e14954 X0 X1 X2 X3
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e14954
        have b1e18685 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e644 X0 X1
             have i₂ := b1e13183 X2 X0 X1
             grind)
          | exact superpose b1e13183 b1e644
          | (have j0 := b1e644 X0 X1
             have j1 := b1e13183 X2 X0 X2
             grind)
          | (have r₁ := b1e644 X1 X2
             have r₂ := b1e13183 X0 X1 X2
             grind)
          | exact resolve b1e644 b1e13183
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e644
        have b1e18849 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e18685 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18685
        have b1e19396 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) X1) ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e26 X1 X0
             have i₂ := b1e18849 X0 (τ X1) X2
             grind)
          | exact superpose b1e18849 b1e26
          | (have j1 := b1e18849 (σ X0) X1 X2
             grind)
          | exact resolve b1e26 b1e18849
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18849
        have b1e37651 : ∀ X0 X1 : G, x ≠ (M.op x X0) ∨ (M.op X1 x) = (k X1 x) := by
          intro X0 X1
          first
          | (have i₁ := b1e20
             have i₂ := b1e14955 X1 x x X0
             grind)
          | (have i₁ := b1e20
             have i₂ := b1e14955 X1 x X0 x
             grind)
          | exact superpose b1e14955 b1e20
          | (have j1 := b1e14955 X1 x x x
             grind)
          | exact resolve b1e20 b1e14955
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e14955
        have b1e37769 : ∀ X1 : G, (M.op X1 x) = (k X1 x) := by
          intro X1
          first
          | (have j0 := b1e37651 x X1
             have j1 := b1e13183 X1 x x
             grind)
          | (have r₁ := b1e37651 x X1
             have r₂ := b1e13183 x x x
             grind)
          | exact resolve b1e37651 b1e13183
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13183 b1e37651
        have b1e37896 : ∀ X0 : G, (k X0 (τ x)) = (τ (M.op (σ X0) x)) := by
          intro X0
          first
          | (have i₁ := b1e158 X0 x
             have i₂ := b1e37769 (σ X0)
             grind)
          | exact superpose b1e37769 b1e158
          | exact resolve b1e158 b1e37769
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e158
        have b1e38065 : ∀ X0 X1 : G, (k (k X0 (τ X1)) (τ x)) = (τ (M.op (k (σ X0) X1) x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e37896 (k X0 (τ X1))
             have i₂ := b1e26 X1 X0
             grind)
          | exact superpose b1e26 b1e37896
          | exact resolve b1e37896 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e37896
        have b1e172145 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) x) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e37769 (σ X0)
             have i₂ := b1e19396 X0 x X1
             grind)
          | exact superpose b1e19396 b1e37769
          | (have j1 := b1e19396 X0 X1 X1
             grind)
          | exact resolve b1e37769 b1e19396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19396
        have b1e184898 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 x) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e172145 (τ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e172145
          | (have j0 := b1e172145 (τ X0) X1
             grind)
          | exact resolve b1e172145 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e172145
        have b1e309680 : ∀ X0 : G, (τ (M.op (M.op (σ X0) x) x)) = (k (k X0 (τ x)) (τ x)) := by
          intro X0
          first
          | (have i₁ := b1e38065 X0 x
             have i₂ := b1e37769 (σ X0)
             grind)
          | exact superpose b1e37769 b1e38065
          | exact resolve b1e38065 b1e37769
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37769 b1e38065
        have b1e309700 : ∀ X0 : G, (τ (M.op (σ X0) (σ y))) = (k (k X0 (τ x)) (τ x)) := by
          intro X0
          first
          | (have i₁ := b1e309680 X0
             have i₂ := b1e127 (σ X0) x x
             grind)
          | exact superpose b1e127 b1e309680
          | exact resolve b1e309680 b1e127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e309680
        have b1e309776 : ∀ X0 : G, (τ (M.op (σ X0) y)) = (k (k X0 (τ x)) (τ x)) := by
          intro X0
          first
          | (have i₁ := b1e309700 X0
             have i₂ := b1e436 (σ X0)
             grind)
          | exact superpose b1e436 b1e309700
          | exact resolve b1e309700 b1e436
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e309700
        have b1e309914 : ∀ X0 : G, (τ (M.op (σ X0) y)) = (M.op (k X0 (τ x)) (τ x)) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b1e184898 x (k X0 (τ x))
             have i₂ := b1e309776 X0
             grind)
          | exact superpose b1e309776 b1e184898
          | (have j0 := b1e184898 x x
             grind)
          | exact resolve b1e184898 b1e309776
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e309776
        have b1e309931 : ∀ X0 : G, (τ (M.op (σ X0) y)) = (M.op (k X0 (τ x)) (τ x)) := by
          intro X0
          first
          | (have j0 := b1e309914 X0
             grind)
          | (have r₁ := b1e309914 X0
             have r₂ := b1e20
             grind)
          | exact resolve b1e309914 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e309914
        have b1e310378 : ∀ X0 : G, (τ (M.op (σ X0) y)) = (M.op (M.op X0 (τ x)) (τ x)) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b1e309931 X0
             have i₂ := b1e184898 x X0
             grind)
          | exact superpose b1e184898 b1e309931
          | (have j1 := b1e184898 x x
             grind)
          | exact resolve b1e309931 b1e184898
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e184898 b1e309931
        have b1e310476 : ∀ X0 : G, (τ (M.op (σ X0) y)) = (M.op (M.op X0 (τ x)) (τ x)) := by
          intro X0
          first
          | (have j0 := b1e310378 X0
             grind)
          | (have r₁ := b1e310378 X0
             have r₂ := b1e20
             grind)
          | exact resolve b1e310378 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e310378
        have b1e310524 : ∀ X0 : G, (M.op X0 (σ y)) = (τ (M.op (σ X0) y)) := by
          intro X0
          first
          | (have i₁ := b1e310476 X0
             have i₂ := b1e127 X0 (τ x) (τ x)
             grind)
          | exact superpose b1e127 b1e310476
          | exact resolve b1e310476 b1e127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e127 b1e310476
        have b1e310555 : ∀ X0 : G, (M.op X0 y) = (τ (M.op (σ X0) y)) := by
          intro X0
          first
          | (have i₁ := b1e310524 X0
             have i₂ := b1e436 X0
             grind)
          | exact superpose b1e436 b1e310524
          | exact resolve b1e310524 b1e436
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e436 b1e310524
        have b1e312325 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) y) := by
          intro X0
          first
          | (have i₁ := b1e13 (M.op (σ X0) y)
             have i₂ := b1e310555 X0
             grind)
          | exact superpose b1e310555 b1e13
          | exact resolve b1e13 b1e310555
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e310555
        have b1e316116 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e491
             have i₂ := b1e312325 x
             grind)
          | exact superpose b1e312325 b1e491
          | (have r₁ := b1e491
             have r₂ := b1e312325 x
             grind)
          | exact resolve b1e491 b1e312325
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e491 b1e312325
        have b1e316219 : False := by grind
        exact b1e316219
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b2e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e18 : y = (M.op y y) := by grind
        have b2e19 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b2e21 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e14 X0 y
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e14
          | (have j0 := b2e14 X0 y
             grind)
          | (have r₁ := b2e14 X0 y
             have r₂ := b2e18
             grind)
          | exact resolve b2e14 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e24 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e21 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21
        have b2e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e29 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
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
        have b2e33 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e29 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e29
          | exact resolve b2e29 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e60 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e33 X0
             have i₂ := b2e15 X0 (σ y)
             grind)
          | exact superpose b2e15 b2e33
          | (have j1 := b2e15 X0 (σ y)
             grind)
          | exact resolve b2e33 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e67 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b2e60 X0
             grind)
          | (have r₁ := b2e60 (σ y)
             have r₂ := b2e19
             grind)
          | (have r₁ := b2e60 X0
             have r₂ := b2e19
             grind)
          | exact resolve b2e60 b2e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e95 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e67 (σ y)
             grind)
          | exact superpose b2e67 b2e19
          | (have r₁ := b2e19
             have r₂ := b2e67 (σ y)
             grind)
          | exact resolve b2e19 b2e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e97 : False := by grind
        exact b2e97
      · have b3e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e18 : y = (M.op y y) := by grind
        have b3e19 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b3e21 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e14 X0 y
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e14
          | (have j0 := b3e14 X0 y
             grind)
          | (have r₁ := b3e14 X0 y
             have r₂ := b3e18
             grind)
          | exact resolve b3e14 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e22 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e21 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e21
        have b3e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b3e56 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e19
             have i₂ := b3e15 X0 (σ y)
             grind)
          | exact superpose b3e15 b3e19
          | (have j1 := b3e15 X0 (σ y)
             grind)
          | (have r₁ := b3e19
             have r₂ := b3e15 X0 (σ y)
             grind)
          | exact resolve b3e19 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e59 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e56 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e111 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e23 X0 y
             have i₂ := b3e22 (τ X0)
             grind)
          | exact superpose b3e22 b3e23
          | exact resolve b3e23 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e22 b3e23
        have b3e117 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e111 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e111
          | exact resolve b3e111 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e111
        have b3e121 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e59 X0
             have i₂ := b3e117 X0
             grind)
          | exact superpose b3e117 b3e59
          | exact resolve b3e59 b3e117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59 b3e117
        have b3e142 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e121 (σ y)
             grind)
          | exact superpose b3e121 b3e19
          | (have r₁ := b3e19
             have r₂ := b3e121 (σ y)
             grind)
          | exact resolve b3e19 b3e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e121
        have b3e146 : False := by grind
        exact b3e146
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b4e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b4e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b4e15 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b4e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b4e18 : y ≠ (M.op y y) := by grind
        have b4e19 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b4e22 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b4e14 X0 (σ y)
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e14
          | (have j0 := b4e14 X0 (σ y)
             grind)
          | (have r₁ := b4e14 X0 (σ y)
             have r₂ := b4e19
             grind)
          | exact resolve b4e14 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e23 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b4e22 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e22
        have b4e28 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b4e16 X0 y
             have i₂ := b4e23 (σ X0)
             grind)
          | exact superpose b4e23 b4e16
          | exact resolve b4e16 b4e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e23
        have b4e31 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b4e12 (k X0 y)
             have i₂ := b4e28 X0
             grind)
          | exact superpose b4e28 b4e12
          | exact resolve b4e12 b4e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e28
        have b4e32 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b4e31 X0
             have i₂ := b4e12 X0
             grind)
          | exact superpose b4e12 b4e31
          | exact resolve b4e31 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e31
        have b4e59 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b4e32 X0
             have i₂ := b4e15 X0 y
             grind)
          | exact superpose b4e15 b4e32
          | (have j1 := b4e15 X0 y
             grind)
          | exact resolve b4e32 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e32
        have b4e64 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b4e59 X0
             grind)
          | (have r₁ := b4e59 y
             have r₂ := b4e18
             grind)
          | (have r₁ := b4e59 X0
             have r₂ := b4e18
             grind)
          | exact resolve b4e59 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e59
        have b4e71 : y ≠ y := by
          first
          | (have i₁ := b4e18
             have i₂ := b4e64 y
             grind)
          | exact superpose b4e64 b4e18
          | (have r₁ := b4e18
             have r₂ := b4e64 y
             grind)
          | exact resolve b4e18 b4e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e64
        have b4e72 : False := by grind
        exact b4e72
      · have b5e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b5e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b5e15 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b5e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b5e18 : y ≠ (M.op y y) := by grind
        have b5e19 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b5e21 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b5e14 X0 (σ y)
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e14
          | (have j0 := b5e14 X0 (σ y)
             grind)
          | (have r₁ := b5e14 X0 (σ y)
             have r₂ := b5e19
             grind)
          | exact resolve b5e14 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e22 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b5e21 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e21
        have b5e26 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b5e22 (σ X0)
             have i₂ := b5e16 X0 y
             grind)
          | exact superpose b5e16 b5e22
          | exact resolve b5e22 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e22
        have b5e29 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b5e12 (k X0 y)
             have i₂ := b5e26 X0
             grind)
          | exact superpose b5e26 b5e12
          | exact resolve b5e12 b5e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e26
        have b5e30 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b5e29 X0
             have i₂ := b5e12 X0
             grind)
          | exact superpose b5e12 b5e29
          | exact resolve b5e29 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e29
        have b5e71 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b5e30 X0
             have i₂ := b5e15 X0 y
             grind)
          | exact superpose b5e15 b5e30
          | (have j1 := b5e15 X0 y
             grind)
          | exact resolve b5e30 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e30
        have b5e75 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b5e71 X0
             grind)
          | (have r₁ := b5e71 y
             have r₂ := b5e18
             grind)
          | (have r₁ := b5e71 X0
             have r₂ := b5e18
             grind)
          | exact resolve b5e71 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e71
        have b5e86 : y ≠ y := by
          first
          | (have i₁ := b5e18
             have i₂ := b5e75 y
             grind)
          | exact superpose b5e75 b5e18
          | (have r₁ := b5e18
             have r₂ := b5e75 y
             grind)
          | exact resolve b5e18 b5e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e75
        have b5e87 : False := by grind
        exact b5e87
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b6e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e18 : y ≠ (M.op y y) := by grind
        have b6e19 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b6e20 : x = (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b6e29 : ∀ X0 X1 : G, (M.op x (M.op X0 x)) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e11 x X0 x X1
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e11
          | exact resolve b6e11 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e37 : ∀ X0 X2 : G, (M.op x X0) = (M.op x X2) := by
          intro X0 X2
          first
          | (have i₁ := b6e29 x X2
             have i₂ := b6e29 x X0
             grind)
          | (have i₁ := b6e29 X0 x
             have i₂ := b6e29 X0 (M.op X0 x)
             grind)
          | exact superpose b6e29 b6e29
          | exact resolve b6e29 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e56 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e19
             have i₂ := b6e15 X0 (σ y)
             grind)
          | exact superpose b6e15 b6e19
          | (have j1 := b6e15 X0 (σ y)
             grind)
          | (have r₁ := b6e19
             have r₂ := b6e15 X0 (σ y)
             grind)
          | exact resolve b6e19 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e59 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e56 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e81 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e20
             have i₂ := b6e37 x X0
             grind)
          | (have i₁ := b6e20
             have i₂ := b6e37 X0 x
             grind)
          | exact superpose b6e37 b6e20
          | exact resolve b6e20 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e90 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e16 X0 y
             have i₂ := b6e59 (σ X0)
             grind)
          | exact superpose b6e59 b6e16
          | exact resolve b6e16 b6e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e2731 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e17
             have i₂ := b6e90 x
             grind)
          | exact superpose b6e90 b6e17
          | exact resolve b6e17 b6e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e90
        have b6e2769 : (σ x) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e2731
             have i₂ := b6e81 y
             grind)
          | exact superpose b6e81 b6e2731
          | exact resolve b6e2731 b6e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2731
        have b6e3211 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e2769
             have i₂ := b6e15 x y
             grind)
          | exact superpose b6e15 b6e2769
          | (have j1 := b6e15 x y
             grind)
          | exact resolve b6e2769 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2769
        have b6e3213 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have r₁ := b6e3211
             have r₂ := b6e18
             grind)
          | exact resolve b6e3211 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3211
        have b6e3216 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b6e3213
             have i₂ := b6e81 y
             grind)
          | exact superpose b6e81 b6e3213
          | exact resolve b6e3213 b6e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81 b6e3213
        have b6e3217 : False := by grind
        exact b6e3217
      · have b7e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b7e15 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b7e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b7e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b7e19 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b7e46 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e14 X1 X0
             have i₂ := b7e15 X2 X0
             grind)
          | exact superpose b7e15 b7e14
          | (have j0 := b7e14 X1 X0
             have j1 := b7e15 X2 X0
             grind)
          | (have r₁ := b7e14 X0 X1
             have r₂ := b7e15 X0 X1
             grind)
          | exact resolve b7e14 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e50 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b7e19
             have i₂ := b7e15 X0 (σ y)
             grind)
          | exact superpose b7e15 b7e19
          | (have j1 := b7e15 X0 (σ y)
             grind)
          | (have r₁ := b7e19
             have r₂ := b7e15 X0 (σ y)
             grind)
          | exact resolve b7e19 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e54 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b7e50 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e50
        have b7e55 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b7e46 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e46
        have b7e57 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b7e16 X0 y
             have i₂ := b7e54 (σ X0)
             grind)
          | exact superpose b7e54 b7e16
          | exact resolve b7e16 b7e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e54
        have b7e184 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have i₁ := b7e19
             have i₂ := b7e57 y
             grind)
          | exact superpose b7e57 b7e19
          | exact resolve b7e19 b7e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e185 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e57 x
             grind)
          | exact superpose b7e57 b7e17
          | exact resolve b7e17 b7e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e57
        have b7e272 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b7e184
             have i₂ := b7e55 y y X0
             grind)
          | exact superpose b7e55 b7e184
          | (have j1 := b7e55 y x X0
             grind)
          | exact resolve b7e184 b7e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e55 b7e184
        have b7e274 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b7e272 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e272
        have b7e871 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b7e185
             have i₂ := b7e274 x
             grind)
          | exact superpose b7e274 b7e185
          | exact resolve b7e185 b7e274
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e185 b7e274
        have b7e877 : False := by grind
        exact b7e877

/-- `Equation4448`: `x ◇ (y ◇ x) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation4448 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4448 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4448.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X0) := by
        intro X0 X1 X2
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op y x) := by grind
      have b0e18 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e36 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 (σ y) (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 y x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : y = (M.op x y) := by
        first
        | (have i₁ := b0e37 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e37
        | exact resolve b0e37 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e126 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e36 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e36
        | exact resolve b0e36 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e160 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e126
           grind)
        | exact superpose b0e126 b0e16
        | exact resolve b0e16 b0e126
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e126
      have b0e171 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e160
           have i₂ := b0e40
           grind)
        | exact superpose b0e40 b0e160
        | exact resolve b0e160 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e160
      have b0e172 : False := by grind
      exact b0e172
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X0) := by
        intro X0 X1 X2
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b1e17 : y = (M.op y x) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e19 : y ≠ y ∨ x = (k x y) := by
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
      have b1e20 : x = (k x y) := by grind
      clear b1e19
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
      have b1e22 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b1e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X0 X2)) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 (M.op X0 X2) X2 X3
           have i₂ := b1e10 X2 X0 X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X2 X0 X3
           have i₂ := b1e10 X2 X0 X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e30 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b1e10 X0 y x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e31 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X3 X2 (M.op X0 X2)
           have i₂ := b1e10 X2 X0 X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e34 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X1 X2) ∨ (k X0 (M.op X1 X2)) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e13 X0 (M.op X1 X2)
           have i₂ := b1e10 X0 X1 X2
           grind)
        | exact superpose b1e10 b1e13
        | (have j0 := b1e13 X0 (M.op X1 X2)
           grind)
        | (have r₁ := b1e13 X0 (M.op X0 (M.op X0 X0))
           have r₂ := b1e10 X0 X0 (M.op X0 X0)
           grind)
        | exact resolve b1e13 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e35 : y = (M.op x y) := by
        first
        | (have i₁ := b1e30 x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e30
        | exact resolve b1e30 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e38 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op y X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 y X1
           have i₂ := b1e30 X0
           grind)
        | exact superpose b1e30 b1e10
        | exact resolve b1e10 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e39 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X1 X0 (M.op y X0)
           have i₂ := b1e30 X0
           grind)
        | exact superpose b1e30 b1e10
        | exact resolve b1e10 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
      have b1e46 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e21 X0 X1
           have i₂ := b1e14 (τ X0) X1
           grind)
        | exact superpose b1e14 b1e21
        | (have j1 := b1e14 (τ X0) X1
           grind)
        | exact resolve b1e21 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21
      have b1e56 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k X0 (τ X1))
           have i₂ := b1e22 X1 X0
           grind)
        | exact superpose b1e22 b1e11
        | exact resolve b1e11 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e72 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e29 X0 X1 X2 (M.op y X0)
           have i₂ := b1e30 X0
           grind)
        | exact superpose b1e30 b1e29
        | exact resolve b1e29 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e95 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e72 X0 X1 X2
           have i₂ := b1e38 X2 X0
           grind)
        | exact superpose b1e38 b1e72
        | exact resolve b1e72 b1e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38 b1e72
      have b1e156 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op (M.op X3 X4) (M.op X2 X3)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e10 (M.op X2 X3) X3 X4
           have i₂ := b1e31 X0 X1 X2 X3
           grind)
        | exact superpose b1e31 b1e10
        | exact resolve b1e10 b1e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e162 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op (M.op X3 X5) (M.op X2 (M.op X3 X4))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b1e29 X3 X4 (M.op X2 (M.op X3 X4)) X5
           have i₂ := b1e31 X0 X1 X2 (M.op X3 X4)
           grind)
        | exact superpose b1e31 b1e29
        | exact resolve b1e29 b1e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e165 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X2 X3) X4) X0) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e29 (M.op X2 X3) X1 X0 X4
           have i₂ := b1e31 X2 X3 X1 X0
           grind)
        | exact superpose b1e31 b1e29
        | exact resolve b1e29 b1e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e29 b1e31
      have b1e178 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e165 X0 X1 x x x
           have i₂ := b1e95 (M.op x x) x X0
           grind)
        | exact superpose b1e95 b1e165
        | exact resolve b1e165 b1e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e165
      have b1e181 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op y (M.op X2 (M.op X3 X4))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e162 X0 X1 X2 X3 X4 x
           have i₂ := b1e95 X3 x (M.op X2 (M.op X3 X4))
           grind)
        | exact superpose b1e95 b1e162
        | exact resolve b1e162 b1e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e162
      have b1e184 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op y (M.op X2 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e156 X0 X1 X2 X3 x
           have i₂ := b1e95 X3 x (M.op X2 X3)
           grind)
        | exact superpose b1e95 b1e156
        | exact resolve b1e156 b1e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e156
      have b1e205 : ∀ X2 X3 X4 : G, (M.op y (M.op X2 (M.op X3 X4))) = (M.op y (M.op X3 X4)) := by
        intro X2 X3 X4
        first
        | (have i₁ := b1e181 x x X2 X3 X4
           have i₂ := b1e95 (M.op x x) X2 (M.op X3 X4)
           grind)
        | exact superpose b1e95 b1e181
        | exact resolve b1e181 b1e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e181
      have b1e207 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op X2 X3)) = (M.op y (M.op (M.op (M.op X0 X1) X2) X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e184 X0 X1 X2 X3
           have i₂ := b1e95 X2 X3 (M.op (M.op (M.op X0 X1) X2) X3)
           grind)
        | exact superpose b1e95 b1e184
        | exact resolve b1e184 b1e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e184
      have b1e214 : ∀ X2 X3 : G, (M.op y (M.op y X3)) = (M.op y (M.op X2 X3)) := by
        intro X2 X3
        first
        | (have i₁ := b1e207 x x X2 X3
           have i₂ := b1e95 (M.op x x) X2 X3
           grind)
        | exact superpose b1e95 b1e207
        | exact resolve b1e207 b1e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e207
      have b1e983 : ∀ X0 : G, (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have j0 := b1e34 X0 X0 (M.op X0 X0)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34
      have b1e984 : ∀ X0 : G, (k X0 (M.op y X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b1e983 X0
           have i₂ := b1e178 X0 X0
           grind)
        | exact superpose b1e178 b1e983
        | exact resolve b1e983 b1e178
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e983
      have b1e1048 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 y) (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b1e984 (M.op X0 y)
           have i₂ := b1e178 y X0
           grind)
        | exact superpose b1e178 b1e984
        | exact resolve b1e984 b1e178
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1604 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e45 X1 X0
           have i₂ := b1e45 X0 X1
           grind)
        | exact superpose b1e45 b1e45
        | (have j0 := b1e45 X1 X0
           have j1 := b1e45 X1 X0
           grind)
        | exact resolve b1e45 b1e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1610 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ X1) X2) (σ (k X0 X1))) = (M.op (σ (k X0 X1)) (M.op (M.op (σ X0) X3) (σ X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e27 (σ X0) X1 (σ X1) X3
           have i₂ := b1e45 X0 X1
           grind)
        | exact superpose b1e45 b1e27
        | (have j1 := b1e45 X0 X1
           grind)
        | exact resolve b1e27 b1e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1611 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (σ X0)) (M.op (M.op X2 X3) (σ X0))) = (M.op (σ (k X0 X1)) (M.op X2 (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e27 X2 X3 (σ X0) (σ X1)
           have i₂ := b1e45 X0 X1
           grind)
        | exact superpose b1e45 b1e27
        | (have j1 := b1e45 X0 X1
           grind)
        | exact resolve b1e27 b1e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27
      have b1e1623 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e95 (σ X0) (σ X1) X2
           have i₂ := b1e45 X0 X1
           grind)
        | exact superpose b1e45 b1e95
        | (have j1 := b1e45 X0 X1
           grind)
        | exact resolve b1e95 b1e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1624 : ∀ X0 X1 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op y (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e178 (σ X1) (σ X0)
           have i₂ := b1e45 X0 X1
           grind)
        | exact superpose b1e45 b1e178
        | (have j1 := b1e45 X0 X1
           grind)
        | exact resolve b1e178 b1e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1645 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b1e45 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e45
      have b1e1672 : ∀ X0 X1 X2 X3 : G, (M.op (σ (k X0 X1)) (M.op X2 (σ X0))) = (M.op y (M.op (M.op X2 X3) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e1611 X0 X1 X2 X3
           have i₂ := b1e95 X2 (σ X0) (M.op (M.op X2 X3) (σ X0))
           grind)
        | exact superpose b1e95 b1e1611
        | (have j0 := b1e1611 X0 X1 X2 X3
           grind)
        | exact resolve b1e1611 b1e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1611
      have b1e1673 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X1) X2) (σ (k X0 X1))) = (M.op (σ (k X0 X1)) (M.op y (σ X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e1610 X0 X1 X2 x
           have i₂ := b1e95 (σ X0) x (σ X1)
           grind)
        | exact superpose b1e95 b1e1610
        | (have j0 := b1e1610 X0 X1 X2 x
           grind)
        | exact resolve b1e1610 b1e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1610
      have b1e1685 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) (M.op X2 (σ X0))) = (M.op y (M.op y (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e1672 X0 X1 X2 x
           have i₂ := b1e214 (M.op X2 x) (σ X0)
           grind)
        | exact superpose b1e214 b1e1672
        | (have j0 := b1e1672 X0 X1 X2 x
           grind)
        | exact resolve b1e1672 b1e214
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1672
      have b1e1686 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (M.op y (σ X1))) = (M.op y (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e1673 X0 X1 x
           have i₂ := b1e95 (σ X1) x (σ (k X0 X1))
           grind)
        | exact superpose b1e95 b1e1673
        | (have j0 := b1e1673 X0 X1 x
           grind)
        | exact resolve b1e1673 b1e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1673
      have b1e1693 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e26 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e26
        | exact resolve b1e26 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e26
      have b1e1711 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op y (σ X0)))) := by
        intro X0
        first
        | (have i₁ := b1e56 X0 (M.op y (σ X0))
           have i₂ := b1e984 (σ X0)
           grind)
        | exact superpose b1e984 b1e56
        | exact resolve b1e56 b1e984
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e56 b1e984
      have b1e1723 : ∀ X0 : G, (k X0 (τ (M.op y (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e1711 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e1711
        | exact resolve b1e1711 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1711
      have b1e2221 : ∀ X0 : G, (M.op y y) = (M.op y (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b1e214 X0 x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e214
        | exact resolve b1e214 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e2229 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op y (M.op X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e214 X2 X1
           have i₂ := b1e214 X0 X1
           grind)
        | (have i₁ := b1e214 X2 x
           have i₂ := b1e214 y x
           grind)
        | exact superpose b1e214 b1e214
        | exact resolve b1e214 b1e214
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e214
      have b1e7019 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
        first
        | (have i₁ := b1e1645 (M.op y y)
           have i₂ := b1e1048 y
           grind)
        | exact superpose b1e1048 b1e1645
        | (have j0 := b1e1645 (M.op y y)
           grind)
        | exact resolve b1e1645 b1e1048
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1645
      have b1e7024 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
      clear b1e7019
      have b1e7063 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e46 (σ X0) X1
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e46
        | exact resolve b1e46 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e46
      have b1e7112 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e7063 X0 X1
           have i₂ := b1e15 X0 X1
           grind)
        | exact superpose b1e15 b1e7063
        | (have j0 := b1e7063 X0 X1
           grind)
        | exact resolve b1e7063 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e7063
      have b1e9061 : ∀ X0 : G, (M.op y X0) = (M.op (σ (M.op y y)) X0) := by
        intro X0
        first
        | (have i₁ := b1e95 (σ (M.op y y)) (σ (M.op y y)) X0
           have i₂ := b1e7024
           grind)
        | exact superpose b1e7024 b1e95
        | exact resolve b1e95 b1e7024
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e9063 : (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op y (σ (M.op y y))) := by
        first
        | (have i₁ := b1e178 (σ (M.op y y)) (σ (M.op y y))
           have i₂ := b1e7024
           grind)
        | exact superpose b1e7024 b1e178
        | exact resolve b1e178 b1e7024
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e178
      have b1e9079 : (σ (M.op y y)) = (M.op y (σ (M.op y y))) := by
        first
        | (have i₁ := b1e9063
           have i₂ := b1e7024
           grind)
        | exact superpose b1e7024 b1e9063
        | exact resolve b1e9063 b1e7024
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e7024 b1e9063
      have b1e11121 : ∀ X0 : G, (M.op y (M.op y (σ x))) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        intro X0
        first
        | (have i₁ := b1e1685 x y X0
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e1685
        | (have j0 := b1e1685 x y x
           grind)
        | exact resolve b1e1685 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1685
      have b1e11280 : ∀ X0 : G, (M.op y (M.op y (σ x))) = (M.op (σ x) (M.op X0 (σ x))) := by
        intro X0
        first
        | (have j0 := b1e11121 X0
           grind)
        | (have r₁ := b1e11121 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e11121 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11121
      have b1e11319 : ∀ X0 : G, (M.op y (M.op y (σ x))) = (M.op (M.op y X0) (σ x)) := by
        intro X0
        first
        | (have i₁ := b1e11280 X0
           have i₂ := b1e39 X0 (σ x)
           grind)
        | exact superpose b1e39 b1e11280
        | exact resolve b1e11280 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e39 b1e11280
      have b1e11345 : (M.op y (σ x)) = (M.op y (M.op y (σ x))) := by
        first
        | (have i₁ := b1e11319 x
           have i₂ := b1e95 y x (σ x)
           grind)
        | exact superpose b1e95 b1e11319
        | exact resolve b1e11319 b1e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e95 b1e11319
      have b1e11487 : (M.op y (σ x)) = (M.op (σ x) (M.op y (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e1686 x y
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e1686
        | (have j0 := b1e1686 x y
           grind)
        | exact resolve b1e1686 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1686
      have b1e11611 : (M.op y (σ x)) = (M.op (σ x) (M.op y (σ y))) := by
        first
        | (have r₁ := b1e11487
           have r₂ := b1e18
           grind)
        | exact resolve b1e11487 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11487
      have b1e12180 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 (σ X1) (σ X0)
           have i₂ := b1e1604 X1 X0
           grind)
        | exact superpose b1e1604 b1e13
        | (have j0 := b1e13 (σ X1) (σ X0)
           have j1 := b1e1604 X1 X0
           grind)
        | (have r₁ := b1e13 (σ X0) (σ X1)
           have r₂ := b1e1604 X0 X1
           grind)
        | exact resolve b1e13 b1e1604
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1604
      have b1e12260 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e12180 X0 X1
           have j1 := b1e13 (σ X1) (σ X0)
           grind)
        | (have r₁ := b1e12180 X0 X1
           have r₂ := b1e13 (σ X1) (σ X0)
           grind)
        | exact resolve b1e12180 b1e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e12180
      have b1e12281 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e12260 X0 X1
           have i₂ := b1e15 X1 X0
           grind)
        | exact superpose b1e15 b1e12260
        | (have j0 := b1e12260 X0 X1
           grind)
        | exact resolve b1e12260 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e12260
      have b1e12282 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e12281 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e12281
      have b1e12299 : (M.op y (M.op y (σ y))) = (M.op y (M.op y (σ x))) := by
        first
        | (have i₁ := b1e205 (σ x) y (σ y)
           have i₂ := b1e11611
           grind)
        | exact superpose b1e11611 b1e205
        | exact resolve b1e205 b1e11611
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11611
      have b1e12392 : (M.op y (M.op y (σ y))) = (M.op y (σ x)) := by
        first
        | (have i₁ := b1e12299
           have i₂ := b1e11345
           grind)
        | exact superpose b1e11345 b1e12299
        | exact resolve b1e12299 b1e11345
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11345 b1e12299
      have b1e12602 : ∀ X0 : G, (M.op y (σ x)) = (M.op y (M.op X0 (σ y))) := by
        intro X0
        first
        | (have i₁ := b1e2229 X0 (σ y) y
           have i₂ := b1e12392
           grind)
        | exact superpose b1e12392 b1e2229
        | exact resolve b1e2229 b1e12392
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2229 b1e12392
      have b1e13642 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e12282 (τ X0) (τ X1)
           have i₂ := b1e1693 X1 X0
           grind)
        | exact superpose b1e1693 b1e12282
        | (have j0 := b1e12282 (τ X0) (τ X1)
           grind)
        | exact resolve b1e12282 b1e1693
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1693 b1e12282
      have b1e13690 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e13642 X0 X1
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e13642
        | (have j0 := b1e13642 X0 X1
           grind)
        | exact resolve b1e13642 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13642
      have b1e13704 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e13690 X0 X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e13690
        | (have j0 := b1e13690 X0 X1
           grind)
        | exact resolve b1e13690 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13690
      have b1e13711 : ∀ X0 X1 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e13704 X0 X1
           have i₂ := b1e22 X0 (τ X1)
           grind)
        | exact superpose b1e22 b1e13704
        | (have j0 := b1e13704 X0 X1
           grind)
        | exact resolve b1e13704 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22 b1e13704
      have b1e13714 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e13711 X0 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e13711
        | (have j0 := b1e13711 X0 X1
           grind)
        | exact resolve b1e13711 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13711
      have b1e13817 : ∀ X0 : G, X0 ≠ X0 ∨ (τ (M.op y (σ X0))) = (k (τ (M.op y (σ X0))) X0) := by
        intro X0
        first
        | (have i₁ := b1e13714 X0 (τ (M.op y (σ X0)))
           have i₂ := b1e1723 X0
           grind)
        | exact superpose b1e1723 b1e13714
        | (have j0 := b1e13714 X0 (τ (M.op y (σ X0)))
           grind)
        | (have r₁ := b1e13714 X0 (τ (M.op y (σ X0)))
           have r₂ := b1e1723 X0
           grind)
        | exact resolve b1e13714 b1e1723
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1723 b1e13714
      have b1e13848 : ∀ X0 : G, (τ (M.op y (σ X0))) = (k (τ (M.op y (σ X0))) X0) := by
        intro X0
        first
        | (have j0 := b1e13817 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13817
      have b1e16832 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        intro X0
        first
        | (have i₁ := b1e1623 x y X0
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e1623
        | (have j0 := b1e1623 x y x
           grind)
        | exact resolve b1e1623 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e1623
      have b1e17037 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b1e16832 X0
           grind)
        | (have r₁ := b1e16832 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e16832 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16832
      have b1e17093 : (σ (M.op x y)) ≠ (M.op y (σ y)) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e17037 (σ y)
           grind)
        | exact superpose b1e17037 b1e16
        | exact resolve b1e16 b1e17037
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17037
      have b1e17236 : (σ y) ≠ (M.op y (σ y)) := by
        first
        | (have i₁ := b1e17093
           have i₂ := b1e35
           grind)
        | exact superpose b1e35 b1e17093
        | exact resolve b1e17093 b1e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17093
      have b1e20623 : ∀ X0 : G, (M.op y (σ (M.op y y))) = (M.op (σ (M.op y y)) (σ (M.op X0 y))) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b1e1624 (M.op X0 y) (M.op y y)
           have i₂ := b1e1048 X0
           grind)
        | exact superpose b1e1048 b1e1624
        | (have j0 := b1e1624 (M.op X0 y) (M.op y y)
           grind)
        | exact resolve b1e1624 b1e1048
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1048 b1e1624
      have b1e20812 : ∀ X0 : G, (M.op y (σ (M.op y y))) = (M.op y (σ (M.op X0 y))) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b1e20623 X0
           have i₂ := b1e9061 (σ (M.op X0 y))
           grind)
        | exact superpose b1e9061 b1e20623
        | (have j0 := b1e20623 X0
           grind)
        | exact resolve b1e20623 b1e9061
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20623
      have b1e20845 : ∀ X0 : G, (σ (M.op y y)) = (M.op y (σ (M.op X0 y))) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b1e20812 X0
           have i₂ := b1e9079
           grind)
        | exact superpose b1e9079 b1e20812
        | (have j0 := b1e20812 X0
           grind)
        | exact resolve b1e20812 b1e9079
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e9079 b1e20812
      have b1e20865 : ∀ X0 : G, (σ (M.op y y)) = (M.op y (σ (M.op X0 y))) ∨ (σ (M.op y y)) = (M.op y (σ (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b1e20845 X0
           have i₂ := b1e9061 (σ (M.op X0 y))
           grind)
        | exact superpose b1e9061 b1e20845
        | (have j0 := b1e20845 X0
           grind)
        | exact resolve b1e20845 b1e9061
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e9061 b1e20845
      have b1e20866 : ∀ X0 : G, (σ (M.op y y)) = (M.op y (σ (M.op X0 y))) := by
        intro X0
        first
        | (have j0 := b1e20865 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20865
      have b1e21242 : (σ (M.op y y)) = (M.op y (σ y)) := by
        first
        | (have i₁ := b1e20866 x
           have i₂ := b1e35
           grind)
        | exact superpose b1e35 b1e20866
        | exact resolve b1e20866 b1e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35
      have b1e21545 : (M.op y (σ y)) = (M.op y (M.op y (σ y))) := by
        first
        | (have i₁ := b1e20866 y
           have i₂ := b1e21242
           grind)
        | exact superpose b1e21242 b1e20866
        | exact resolve b1e20866 b1e21242
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e21546 : (M.op y y) = (τ (M.op y (σ y))) := by
        first
        | (have i₁ := b1e11 (M.op y y)
           have i₂ := b1e21242
           grind)
        | exact superpose b1e21242 b1e11
        | exact resolve b1e11 b1e21242
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e21644 : (M.op y (σ y)) = (M.op y (σ x)) := by
        first
        | (have i₁ := b1e21545
           have i₂ := b1e12602 y
           grind)
        | exact superpose b1e12602 b1e21545
        | exact resolve b1e21545 b1e12602
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e12602 b1e21545
      have b1e22295 : (τ (M.op y (σ y))) = (k (τ (M.op y (σ y))) x) := by
        first
        | (have i₁ := b1e13848 x
           have i₂ := b1e21644
           grind)
        | exact superpose b1e21644 b1e13848
        | exact resolve b1e13848 b1e21644
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13848 b1e21644
      have b1e22411 : (M.op y y) = (k (M.op y y) x) := by
        first
        | (have i₁ := b1e22295
           have i₂ := b1e21546
           grind)
        | exact superpose b1e21546 b1e22295
        | exact resolve b1e22295 b1e21546
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21546 b1e22295
      have b1e23553 : (σ (M.op y y)) = (σ (M.op (M.op y y) x)) ∨ x = (M.op x (M.op y y)) := by
        first
        | (have i₁ := b1e7112 (M.op y y) x
           have i₂ := b1e22411
           grind)
        | exact superpose b1e22411 b1e7112
        | (have j0 := b1e7112 (M.op y y) x
           grind)
        | exact resolve b1e7112 b1e22411
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e7112 b1e22411
      have b1e23562 : (σ (M.op y y)) = (σ (M.op x (M.op y x))) ∨ x = (M.op x (M.op y y)) := by
        first
        | (have i₁ := b1e23553
           have i₂ := b1e10 x y y
           grind)
        | exact superpose b1e10 b1e23553
        | exact resolve b1e23553 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23553
      have b1e23572 : (σ (M.op y y)) = (σ (M.op y x)) ∨ x = (M.op x (M.op y y)) := by
        first
        | (have i₁ := b1e23562
           have i₂ := b1e30 x
           grind)
        | exact superpose b1e30 b1e23562
        | exact resolve b1e23562 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30 b1e23562
      have b1e23580 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x (M.op y y)) := by
        first
        | (have i₁ := b1e23572
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e23572
        | exact resolve b1e23572 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23572
      have b1e23587 : (σ y) = (M.op y (σ y)) ∨ x = (M.op x (M.op y y)) := by
        first
        | (have i₁ := b1e23580
           have i₂ := b1e21242
           grind)
        | exact superpose b1e21242 b1e23580
        | exact resolve b1e23580 b1e21242
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21242 b1e23580
      have b1e23590 : x = (M.op x (M.op y y)) := by
        first
        | (have r₁ := b1e23587
           have r₂ := b1e17236
           grind)
        | exact resolve b1e23587 b1e17236
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23587
      have b1e23933 : ∀ X0 : G, (M.op y x) = (M.op y (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b1e205 x x (M.op y y)
           have i₂ := b1e23590
           grind)
        | exact superpose b1e23590 b1e205
        | exact resolve b1e205 b1e23590
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e205 b1e23590
      have b1e23970 : (M.op y x) = (M.op y y) := by
        first
        | (have i₁ := b1e23933 x
           have i₂ := b1e2221 x
           grind)
        | exact superpose b1e2221 b1e23933
        | exact resolve b1e23933 b1e2221
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2221 b1e23933
      have b1e24018 : y = (M.op y y) := by
        first
        | (have i₁ := b1e23970
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e23970
        | exact resolve b1e23970 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23970
      have b1e24725 : (σ y) = (M.op y (σ y)) := by
        first
        | (have i₁ := b1e20866 y
           have i₂ := b1e24018
           grind)
        | exact superpose b1e24018 b1e20866
        | exact resolve b1e20866 b1e24018
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20866 b1e24018
      have b1e24800 : False := by grind
      exact b1e24800
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X0) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e17 : y ≠ (M.op y x) := by grind
      have b2e18 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e19 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
      have b2e20 : (σ x) = (k (σ x) (σ y)) := by grind
      clear b2e19
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
      have b2e30 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ x)) := by
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
      have b2e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X0 X2)) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 (M.op X0 X2) X2 X3
           have i₂ := b2e10 X2 X0 X1
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X2 X0 X3
           have i₂ := b2e10 X2 X0 X1
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e34 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b2e10 X0 (σ y) (σ x)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X3 X2 (M.op X0 X2)
           have i₂ := b2e10 X2 X0 X1
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e38 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X1 X2) ∨ (k X0 (M.op X1 X2)) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e13 X0 (M.op X1 X2)
           have i₂ := b2e10 X0 X1 X2
           grind)
        | exact superpose b2e10 b2e13
        | (have j0 := b2e13 X0 (M.op X1 X2)
           grind)
        | (have r₁ := b2e13 X0 (M.op X0 (M.op X0 X0))
           have r₂ := b2e10 X0 X0 (M.op X0 X0)
           grind)
        | exact resolve b2e13 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
      have b2e47 : x = (M.op x y) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b2e27
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e27
        | (have j1 := b2e14 y x
           grind)
        | exact resolve b2e27 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27
      have b2e50 : x = (M.op x y) := by
        first
        | (have r₁ := b2e47
           have r₂ := b2e17
           grind)
        | exact resolve b2e47 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47
      have b2e52 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b2e10 X0 x y
           have i₂ := b2e50
           grind)
        | exact superpose b2e50 b2e10
        | exact resolve b2e10 b2e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e80 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (σ y) X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e33 (σ y) X0 X1 (σ x)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e33
        | exact resolve b2e33 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e81 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op x X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e33 x X0 X1 y
           have i₂ := b2e50
           grind)
        | exact superpose b2e50 b2e33
        | exact resolve b2e33 b2e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e102 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b2e34 (σ x)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e34
        | exact resolve b2e34 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e110 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op (M.op X0 X2) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e33 X0 (M.op (σ y) X0) X1 X2
           have i₂ := b2e34 X0
           grind)
        | exact superpose b2e34 b2e33
        | exact resolve b2e33 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e33
      have b2e111 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X1 X0 (M.op (σ y) X0)
           have i₂ := b2e34 X0
           grind)
        | exact superpose b2e34 b2e10
        | exact resolve b2e10 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34
      have b2e117 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e111 X0 X1
           have i₂ := b2e80 X0 X1
           grind)
        | exact superpose b2e80 b2e111
        | exact resolve b2e111 b2e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e111
      have b2e118 : ∀ X0 X1 X2 : G, (M.op (σ y) X1) = (M.op (M.op X0 X2) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e110 X0 X1 X2
           have i₂ := b2e80 X0 X1
           grind)
        | exact superpose b2e80 b2e110
        | exact resolve b2e110 b2e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e80 b2e110
      have b2e194 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op (M.op X3 X4) (M.op X2 X3)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e10 (M.op X2 X3) X3 X4
           have i₂ := b2e35 X0 X1 X2 X3
           grind)
        | exact superpose b2e35 b2e10
        | exact resolve b2e10 b2e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e220 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op (σ y) (M.op X2 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e194 X0 X1 X2 X3 x
           have i₂ := b2e118 X3 (M.op X2 X3) x
           grind)
        | exact superpose b2e118 b2e194
        | exact resolve b2e194 b2e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e194
      have b2e243 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) (M.op X2 X3)) = (M.op (σ y) (M.op (M.op (M.op X0 X1) X2) X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e220 X0 X1 X2 X3
           have i₂ := b2e118 X2 (M.op (M.op (M.op X0 X1) X2) X3) X3
           grind)
        | exact superpose b2e118 b2e220
        | exact resolve b2e220 b2e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e220
      have b2e251 : ∀ X2 X3 : G, (M.op (σ y) (M.op X2 X3)) = (M.op (σ y) (M.op (σ y) X3)) := by
        intro X2 X3
        first
        | (have i₁ := b2e243 x x X2 X3
           have i₂ := b2e118 (M.op x x) X3 X2
           grind)
        | exact superpose b2e118 b2e243
        | exact resolve b2e243 b2e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e243
      have b2e254 : x = (M.op y x) := by
        first
        | (have i₁ := b2e52 y
           have i₂ := b2e50
           grind)
        | exact superpose b2e50 b2e52
        | exact resolve b2e52 b2e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e261 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op (M.op X1 X2) x) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e35 X1 X2 x X0
           have i₂ := b2e52 X0
           grind)
        | exact superpose b2e52 b2e35
        | exact resolve b2e35 b2e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e273 : (M.op (σ x) (σ y)) = (M.op (M.op x (σ y)) (σ x)) := by
        first
        | (have i₁ := b2e30 (M.op x (σ y))
           have i₂ := b2e52 (σ y)
           grind)
        | exact superpose b2e52 b2e30
        | exact resolve b2e30 b2e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e30
      have b2e276 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x (σ x))) := by
        first
        | (have i₁ := b2e273
           have i₂ := b2e10 (σ x) x (σ y)
           grind)
        | exact superpose b2e10 b2e273
        | exact resolve b2e273 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e273
      have b2e285 : ∀ X0 : G, (M.op (σ y) X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b2e261 X0 x x
           have i₂ := b2e118 (M.op x x) X0 x
           grind)
        | exact superpose b2e118 b2e261
        | exact resolve b2e261 b2e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e261
      have b2e291 : (M.op (σ x) (σ y)) = (M.op x (σ x)) := by
        first
        | (have i₁ := b2e276
           have i₂ := b2e52 (σ x)
           grind)
        | exact superpose b2e52 b2e276
        | exact resolve b2e276 b2e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e276
      have b2e298 : (σ y) = (M.op x (σ x)) := by
        first
        | (have i₁ := b2e291
           have i₂ := b2e102
           grind)
        | exact superpose b2e102 b2e291
        | exact resolve b2e291 b2e102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e102 b2e291
      have b2e519 : x ≠ y := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e254
           grind)
        | exact superpose b2e254 b2e17
        | exact resolve b2e17 b2e254
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e906 : ∀ X0 : G, (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have j0 := b2e38 X0 X0 (M.op X0 X0)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e38
      have b2e907 : ∀ X0 : G, (k X0 (M.op (σ y) X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b2e906 X0
           have i₂ := b2e117 X0 X0
           grind)
        | exact superpose b2e117 b2e906
        | exact resolve b2e906 b2e117
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e906
      have b2e941 : ∀ X0 : G, (k X0 (M.op x X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b2e907 X0
           have i₂ := b2e285 X0
           grind)
        | exact superpose b2e285 b2e907
        | exact resolve b2e907 b2e285
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e907
      have b2e1113 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op (M.op X3 X4) (M.op X2 X3)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e31 X2 (M.op X0 X2) X3 X4
           have i₂ := b2e10 X2 X0 X1
           grind)
        | exact superpose b2e10 b2e31
        | exact resolve b2e31 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e31
      have b2e1260 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op (σ y) (M.op X2 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e1113 X0 X1 X2 X3 x
           have i₂ := b2e118 X3 (M.op X2 X3) x
           grind)
        | exact superpose b2e118 b2e1113
        | exact resolve b2e1113 b2e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1113
      have b2e1355 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op x (M.op X2 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e1260 X0 X1 X2 X3
           have i₂ := b2e285 (M.op X2 X3)
           grind)
        | exact superpose b2e285 b2e1260
        | exact resolve b2e1260 b2e285
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1260
      have b2e1440 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op x (M.op X2 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e1355 X0 X1 X2 X3
           have i₂ := b2e118 X2 (M.op (M.op (M.op X0 X1) X2) X3) X3
           grind)
        | exact superpose b2e118 b2e1355
        | exact resolve b2e1355 b2e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1355
      have b2e1508 : ∀ X2 X3 : G, (M.op (σ y) (M.op (σ y) X3)) = (M.op x (M.op X2 X3)) := by
        intro X2 X3
        first
        | (have i₁ := b2e1440 x x X2 X3
           have i₂ := b2e251 (M.op (M.op x x) X2) X3
           grind)
        | exact superpose b2e251 b2e1440
        | exact resolve b2e1440 b2e251
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e251 b2e1440
      have b2e1555 : ∀ X2 X3 : G, (M.op x (M.op X2 X3)) = (M.op x (M.op (σ y) X3)) := by
        intro X2 X3
        first
        | (have i₁ := b2e1508 X2 X3
           have i₂ := b2e285 (M.op (σ y) X3)
           grind)
        | exact superpose b2e285 b2e1508
        | exact resolve b2e1508 b2e285
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1508
      have b2e1587 : ∀ X2 X3 : G, (M.op x (M.op X2 X3)) = (M.op x (M.op x X3)) := by
        intro X2 X3
        first
        | (have i₁ := b2e1555 X2 X3
           have i₂ := b2e285 X3
           grind)
        | exact superpose b2e285 b2e1555
        | exact resolve b2e1555 b2e285
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1555
      have b2e1763 : ∀ X0 X1 X2 X3 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op (M.op (M.op X2 X3) (σ X0)) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e35 X2 X3 (σ X0) (σ X1)
           have i₂ := b2e45 X0 X1
           grind)
        | exact superpose b2e45 b2e35
        | (have j1 := b2e45 X0 X1
           grind)
        | exact resolve b2e35 b2e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e35
      have b2e1791 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b2e45 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e45
      have b2e1814 : ∀ X0 X1 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op (σ y) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e1763 X0 X1 x x
           have i₂ := b2e118 (M.op x x) (σ X1) (σ X0)
           grind)
        | exact superpose b2e118 b2e1763
        | (have j0 := b2e1763 X0 X1 x x
           grind)
        | exact resolve b2e1763 b2e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1763
      have b2e1853 : ∀ X0 X1 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op x (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e1814 X0 X1
           have i₂ := b2e285 (σ X1)
           grind)
        | exact superpose b2e285 b2e1814
        | (have j0 := b2e1814 X0 X1
           grind)
        | exact resolve b2e1814 b2e285
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1814
      have b2e2172 : ∀ X0 : G, (M.op X0 x) = (k (M.op X0 x) (M.op (σ y) x)) := by
        intro X0
        first
        | (have i₁ := b2e941 (M.op X0 x)
           have i₂ := b2e117 X0 x
           grind)
        | exact superpose b2e117 b2e941
        | exact resolve b2e941 b2e117
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e117
      have b2e2175 : ∀ X0 : G, (M.op X0 x) = (k (M.op X0 x) (M.op x x)) := by
        intro X0
        first
        | (have i₁ := b2e2172 X0
           have i₂ := b2e285 x
           grind)
        | exact superpose b2e285 b2e2172
        | exact resolve b2e2172 b2e285
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2172
      have b2e2628 : ∀ X0 X1 : G, (M.op x X1) = (k (M.op x X1) (M.op x (M.op X0 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e941 (M.op x X1)
           have i₂ := b2e1587 X0 X1
           grind)
        | (have i₁ := b2e941 (M.op x x)
           have i₂ := b2e1587 x x
           grind)
        | exact superpose b2e1587 b2e941
        | exact resolve b2e941 b2e1587
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e941 b2e1587
      have b2e7376 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
        first
        | (have i₁ := b2e1791 (M.op x x)
           have i₂ := b2e2175 x
           grind)
        | exact superpose b2e2175 b2e1791
        | (have j0 := b2e1791 (M.op x x)
           grind)
        | exact resolve b2e1791 b2e2175
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1791
      have b2e7381 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by grind
      clear b2e7376
      have b2e13911 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x x)) X0) := by
        intro X0
        first
        | (have i₁ := b2e118 (σ (M.op x x)) X0 (σ (M.op x x))
           have i₂ := b2e7381
           grind)
        | exact superpose b2e7381 b2e118
        | exact resolve b2e118 b2e7381
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e118
      have b2e13932 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x x)) X0) := by
        intro X0
        first
        | (have i₁ := b2e13911 X0
           have i₂ := b2e285 X0
           grind)
        | exact superpose b2e285 b2e13911
        | exact resolve b2e13911 b2e285
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e285 b2e13911
      have b2e14231 : (σ (M.op x x)) = (M.op x (σ (M.op x x))) := by
        first
        | (have i₁ := b2e7381
           have i₂ := b2e13932 (σ (M.op x x))
           grind)
        | exact superpose b2e13932 b2e7381
        | exact resolve b2e7381 b2e13932
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e7381
      have b2e15585 : ∀ X0 : G, (M.op (σ (M.op x x)) (σ (M.op X0 x))) = (M.op x (σ (M.op x x))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op X0 x))) := by
        intro X0
        first
        | (have i₁ := b2e1853 (M.op X0 x) (M.op x x)
           have i₂ := b2e2175 X0
           grind)
        | exact superpose b2e2175 b2e1853
        | (have j0 := b2e1853 (M.op X0 x) (M.op x x)
           grind)
        | exact resolve b2e1853 b2e2175
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1853 b2e2175
      have b2e15745 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op X0 x))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op X0 x))) := by
        intro X0
        first
        | (have i₁ := b2e15585 X0
           have i₂ := b2e14231
           grind)
        | exact superpose b2e14231 b2e15585
        | (have j0 := b2e15585 X0
           grind)
        | exact resolve b2e15585 b2e14231
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e14231 b2e15585
      have b2e15746 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op X0 x))) := by
        intro X0
        first
        | (have j0 := b2e15745 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e15745
      have b2e15777 : ∀ X0 : G, (σ (M.op x x)) = (M.op x (σ (M.op X0 x))) := by
        intro X0
        first
        | (have i₁ := b2e15746 X0
           have i₂ := b2e13932 (σ (M.op X0 x))
           grind)
        | exact superpose b2e13932 b2e15746
        | exact resolve b2e15746 b2e13932
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e13932 b2e15746
      have b2e15823 : (M.op x (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b2e15777 y
           have i₂ := b2e254
           grind)
        | exact superpose b2e254 b2e15777
        | exact resolve b2e15777 b2e254
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e254 b2e15777
      have b2e15946 : (σ y) = (σ (M.op x x)) := by
        first
        | (have i₁ := b2e15823
           have i₂ := b2e298
           grind)
        | exact superpose b2e298 b2e15823
        | exact resolve b2e15823 b2e298
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e298 b2e15823
      have b2e16339 : (M.op x x) = (τ (σ y)) := by
        first
        | (have i₁ := b2e11 (M.op x x)
           have i₂ := b2e15946
           grind)
        | exact superpose b2e15946 b2e11
        | exact resolve b2e11 b2e15946
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e15946
      have b2e16395 : y = (M.op x x) := by
        first
        | (have i₁ := b2e16339
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e16339
        | exact resolve b2e16339 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16339
      have b2e16494 : y = (M.op x y) := by
        first
        | (have i₁ := b2e52 x
           have i₂ := b2e16395
           grind)
        | exact superpose b2e16395 b2e52
        | exact resolve b2e52 b2e16395
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e52
      have b2e16495 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b2e81 x X0
           have i₂ := b2e16395
           grind)
        | exact superpose b2e16395 b2e81
        | exact resolve b2e81 b2e16395
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e81
      have b2e16594 : y = (M.op y y) := by
        first
        | (have i₁ := b2e16494
           have i₂ := b2e16495 y
           grind)
        | exact superpose b2e16495 b2e16494
        | exact resolve b2e16494 b2e16495
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16494 b2e16495
      have b2e17131 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
        first
        | (have i₁ := b2e2628 y y
           have i₂ := b2e16594
           grind)
        | exact superpose b2e16594 b2e2628
        | exact resolve b2e2628 b2e16594
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2628 b2e16594
      have b2e17142 : x = (k x x) := by
        first
        | (have i₁ := b2e17131
           have i₂ := b2e50
           grind)
        | exact superpose b2e50 b2e17131
        | exact resolve b2e17131 b2e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50 b2e17131
      have b2e17667 : x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b2e14 x x
           have i₂ := b2e17142
           grind)
        | exact superpose b2e17142 b2e14
        | (have j0 := b2e14 x x
           grind)
        | exact resolve b2e14 b2e17142
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e17142
      have b2e17668 : x = (M.op x x) := by grind
      clear b2e17667
      have b2e17672 : x = y := by
        first
        | (have i₁ := b2e17668
           have i₂ := b2e16395
           grind)
        | exact superpose b2e16395 b2e17668
        | exact resolve b2e17668 b2e16395
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16395 b2e17668
      have b2e17678 : False := by grind
      exact b2e17678
    · have b3e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op y x) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e33 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X0 X1
           have i₂ := b3e14 (σ X0) (σ X1)
           grind)
        | exact superpose b3e14 b3e15
        | (have j1 := b3e14 (σ X0) (σ X1)
           grind)
        | exact resolve b3e15 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e770 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e33 x y
           grind)
        | exact superpose b3e33 b3e16
        | (have j1 := b3e33 x y
           grind)
        | exact resolve b3e16 b3e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e33
      have b3e821 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have r₁ := b3e770
           have r₂ := b3e18
           grind)
        | exact resolve b3e770 b3e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e770
      have b3e826 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b3e821
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e821
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e821 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e821
      have b3e827 : y = (M.op y x) := by grind
      clear b3e826
      have b3e828 : False := by grind
      exact b3e828

/-- `Equation4456`: `x ◇ (y ◇ x) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4456 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4456 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4456.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
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
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
      have b0e26 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
        intro X0
        grind
      clear b0e23
      have b0e30 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e26 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e26
        | exact resolve b0e26 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26
      have b0e33 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e10 (σ x) (σ x) X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X2 X1 X3
           have i₂ := b0e10 X2 X1 X0
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X3 (M.op X1 X2) X2
           have i₂ := b0e10 X2 X1 X0
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 (σ x) (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 x x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e38 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e38
        | exact resolve b0e38 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e52 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e53 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 X2 X2
           have i₂ := b0e14 X2 X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op X2 X1)
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X2 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
      have b0e59 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op (M.op x y) X0) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 x y
           have i₂ := b0e39
           grind)
        | exact superpose b0e39 b0e10
        | exact resolve b0e10 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e60 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x y) X0) := by
        intro X0
        first
        | (have i₁ := b0e59 X0
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e59
        | exact resolve b0e59 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e59
      have b0e67 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e110 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e34 X0 (σ x) X1 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e34
        | exact resolve b0e34 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e148 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 y x
           have i₂ := b0e60 X0
           grind)
        | exact superpose b0e60 b0e10
        | exact resolve b0e10 b0e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60
      have b0e166 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e37 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e37
        | exact resolve b0e37 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e224 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e24 X1 X0
           have i₂ := b0e52 (τ X1) X0
           grind)
        | exact superpose b0e52 b0e24
        | (have j1 := b0e52 (τ X1) X0
           grind)
        | exact resolve b0e24 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24
      have b0e228 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e52 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52
      have b0e231 : (M.op x y) = (M.op x (M.op x y)) := by
        first
        | (have i₁ := b0e148 x
           have i₂ := b0e39
           grind)
        | exact superpose b0e39 b0e148
        | exact resolve b0e148 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e148
      have b0e412 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e30 X1
           have i₂ := b0e14 (τ X1) X0
           grind)
        | (have i₁ := b0e30 X0
           have i₂ := b0e14 X0 (M.op (τ X0) (τ X0))
           grind)
        | exact superpose b0e14 b0e30
        | (have j1 := b0e14 (τ X1) X0
           grind)
        | exact resolve b0e30 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e636 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b0e67
      have b0e650 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e636 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e636
        | exact resolve b0e636 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e636
      have b0e672 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ x)) (σ x)) X0) = (M.op X0 (M.op (σ y) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e35 X1 (σ x) (σ x) X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e35
        | exact resolve b0e35 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e830 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e672 X0 x
           have i₂ := b0e110 (M.op x (σ x)) X0
           grind)
        | exact superpose b0e110 b0e672
        | exact resolve b0e672 b0e110
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e110 b0e672
      have b0e868 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X1) ∨ (M.op X3 X1) = (k (M.op X3 X1) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e228 (M.op X3 X1) X2
           have i₂ := b0e34 X3 X1 X2 X0
           grind)
        | (have i₁ := b0e228 (M.op X3 X1) X2
           have i₂ := b0e34 X0 X1 X2 X3
           grind)
        | exact superpose b0e34 b0e228
        | (have j0 := b0e228 (M.op X3 X1) X2
           grind)
        | (have r₁ := b0e228 (M.op (M.op X3 X2) X2) X2
           have r₂ := b0e34 (M.op X3 X2) X2 X2 X3
           grind)
        | (have r₁ := b0e228 (M.op (M.op X0 X2) X2) X2
           have r₂ := b0e34 X0 X2 X2 (M.op X0 X2)
           grind)
        | exact resolve b0e228 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34 b0e228
      have b0e916 : ∀ X0 : G, (M.op X0 x) = (M.op x (M.op x y)) ∨ (M.op y X0) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b0e53 X0 x y
           have i₂ := b0e39
           grind)
        | exact superpose b0e39 b0e53
        | (have j0 := b0e53 X0 x y
           grind)
        | exact resolve b0e53 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53
      have b0e1010 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op x y) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b0e916 X0
           have i₂ := b0e231
           grind)
        | exact superpose b0e231 b0e916
        | (have j0 := b0e916 X0
           grind)
        | exact resolve b0e916 b0e231
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e231 b0e916
      have b0e1642 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e650 X1
           have i₂ := b0e56 X1 X0
           grind)
        | exact superpose b0e56 b0e650
        | (have j1 := b0e56 X1 X0
           grind)
        | exact resolve b0e650 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e650
      have b0e1661 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e56 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1665 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e1642 X0 X1
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e1642
        | (have j0 := b0e1642 X0 X1
           grind)
        | exact resolve b0e1642 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1642
      have b0e1923 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e830 (σ y)
           have i₂ := b0e56 y x
           grind)
        | exact superpose b0e56 b0e830
        | (have j1 := b0e56 y X0
           grind)
        | exact resolve b0e830 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56 b0e830
      have b0e23594 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e224 X0 (σ X0)
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e224
        | exact resolve b0e224 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e224
      have b0e23700 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e23594 X0 X1
           have i₂ := b0e15 X1 X0
           grind)
        | exact superpose b0e15 b0e23594
        | (have j0 := b0e23594 X0 X1
           grind)
        | exact resolve b0e23594 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23594
      have b0e148873 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e412 X0 (σ X0)
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e412
        | (have j0 := b0e412 X1 (σ X0)
           grind)
        | exact resolve b0e412 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e412
      have b0e148907 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e148873 X0 X1
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e148873
        | (have j0 := b0e148873 X0 X1
           grind)
        | exact resolve b0e148873 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e148873
      have b0e149148 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e1661 X0
           have i₂ := b0e148907 X0 X0
           grind)
        | exact superpose b0e148907 b0e1661
        | (have j0 := b0e1661 X0
           have j1 := b0e148907 X0 X0
           grind)
        | (have r₁ := b0e1661 x
           have r₂ := b0e148907 x x
           grind)
        | exact resolve b0e1661 b0e148907
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1661 b0e148907
      have b0e149184 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e149148 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e149148
      have b0e248794 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e166
           have i₂ := b0e1665 x y
           grind)
        | exact superpose b0e1665 b0e166
        | (have j1 := b0e1665 x y
           grind)
        | exact resolve b0e166 b0e1665
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1665
      have b0e283307 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (k x x) := by
        first
        | (have i₁ := b0e33 (σ x)
           have i₂ := b0e149184 x
           grind)
        | exact superpose b0e149184 b0e33
        | (have j1 := b0e149184 x
           grind)
        | exact resolve b0e33 b0e149184
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e149184
      have b0e283369 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (k x x) := by
        first
        | (have i₁ := b0e283307
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e283307
        | exact resolve b0e283307 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e283307
      have b0e283385 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e283369
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e283369
        | exact resolve b0e283369 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e283369
      have b0e286505 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e283385
           grind)
        | exact superpose b0e283385 b0e16
        | exact resolve b0e16 b0e283385
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e283385
      have b0e300486 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e248794
           grind)
        | exact superpose b0e248794 b0e16
        | exact resolve b0e16 b0e248794
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e248794
      have b0e303880 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e300486
           have i₂ := b0e1010 x
           grind)
        | exact superpose b0e1010 b0e300486
        | (have j1 := b0e1010 x
           grind)
        | exact resolve b0e300486 b0e1010
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1010
      have b0e303887 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k y x) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e300486
           have i₂ := b0e23700 x y
           grind)
        | exact superpose b0e23700 b0e300486
        | (have j1 := b0e23700 x y
           grind)
        | exact resolve b0e300486 b0e23700
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23700 b0e300486
      have b0e303889 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k y x) := by grind
      clear b0e303887
      have b0e303892 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e303889
           have i₂ := b0e39
           grind)
        | exact superpose b0e39 b0e303889
        | exact resolve b0e303889 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e303889
      have b0e303893 : y = (k y x) := by grind
      clear b0e303892
      have b0e303897 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e303880
           have i₂ := b0e39
           grind)
        | exact superpose b0e39 b0e303880
        | exact resolve b0e303880 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e303880
      have b0e303898 : y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e303897
      have b0e303904 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e303898
           have i₂ := b0e39
           grind)
        | exact superpose b0e39 b0e303898
        | exact resolve b0e303898 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e303898
      have b0e303907 : y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e303904
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e303904
        | exact resolve b0e303904 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e303904
      have b0e303908 : y = (M.op x y) := by grind
      clear b0e303907
      have b0e310345 : (σ y) ≠ (σ y) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e286505
           have i₂ := b0e303908
           grind)
        | exact superpose b0e303908 b0e286505
        | exact resolve b0e286505 b0e303908
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e286505
      have b0e310558 : y = (k x x) := by grind
      clear b0e310345
      have b0e738186 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op (M.op X0 X1) X1) X1) := by
        intro X0 X1
        first
        | (have j0 := b0e868 X0 X1 X1 (M.op X0 X1)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e868
      have b0e738285 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
        first
        | (have i₁ := b0e738186 x (σ x)
           have i₂ := b0e33 x
           grind)
        | exact superpose b0e33 b0e738186
        | exact resolve b0e738186 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e738186
      have b0e738750 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e1923 x
           have i₂ := b0e166
           grind)
        | exact superpose b0e166 b0e1923
        | exact resolve b0e1923 b0e166
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e166 b0e1923
      have b0e738761 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e738750
           have i₂ := b0e303893
           grind)
        | exact superpose b0e303893 b0e738750
        | exact resolve b0e738750 b0e303893
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e303893 b0e738750
      have b0e741957 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e738761
           grind)
        | exact superpose b0e738761 b0e16
        | exact resolve b0e16 b0e738761
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e738761
      have b0e741969 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e741957
           have i₂ := b0e303908
           grind)
        | exact superpose b0e303908 b0e741957
        | exact resolve b0e741957 b0e303908
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e741957
      have b0e741970 : (σ x) = (M.op (σ x) (σ y)) := by grind
      clear b0e741969
      have b0e741991 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e741970
           grind)
        | exact superpose b0e741970 b0e16
        | exact resolve b0e16 b0e741970
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e742007 : (σ x) = (k (σ x) (σ x)) := by
        first
        | (have i₁ := b0e738285
           have i₂ := b0e741970
           grind)
        | exact superpose b0e741970 b0e738285
        | exact resolve b0e738285 b0e741970
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e738285 b0e741970
      have b0e742288 : (σ x) = (σ (k x x)) := by
        first
        | (have i₁ := b0e742007
           have i₂ := b0e15 x x
           grind)
        | exact superpose b0e15 b0e742007
        | exact resolve b0e742007 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e742007
      have b0e742292 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b0e741991
           have i₂ := b0e303908
           grind)
        | exact superpose b0e303908 b0e741991
        | exact resolve b0e741991 b0e303908
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e303908 b0e741991
      have b0e742354 : (σ x) = (σ y) := by
        first
        | (have i₁ := b0e742288
           have i₂ := b0e310558
           grind)
        | exact superpose b0e310558 b0e742288
        | exact resolve b0e742288 b0e310558
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e310558 b0e742288
      have b0e742386 : False := by grind
      exact b0e742386
    · have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b1e17 : y = (M.op x x) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e20 : x = (k x y) := by grind
      have b1e22 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b1e47 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e50 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
      have b1e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
      have b1e62 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k X0 (τ X1))
           have i₂ := b1e22 X1 X0
           grind)
        | exact superpose b1e22 b1e11
        | exact resolve b1e11 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22
      have b1e165 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e47 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e47
      have b1e300 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b1e50 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e50
      have b1e301 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e300
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e300
        | exact resolve b1e300 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e300
      have b1e302 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e301
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e301
        | exact resolve b1e301 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e301
      have b1e303 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e302
           grind)
        | exact superpose b1e302 b1e16
        | exact resolve b1e16 b1e302
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e302
      have b1e1258 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b1e62
      have b1e1274 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e1258 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e1258
        | exact resolve b1e1258 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1258
      have b1e1327 : x ≠ y ∨ x = (k x x) := by
        first
        | (have i₁ := b1e165 x x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e165
        | (have j0 := b1e165 x x
           grind)
        | exact resolve b1e165 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e165
      have b1e1358 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e51 x x
           grind)
        | exact superpose b1e51 b1e18
        | (have j1 := b1e51 x x
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e51 x y
           grind)
        | exact resolve b1e18 b1e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e51
      have b1e11170 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e1358
           have i₂ := b1e14 x x
           grind)
        | exact superpose b1e14 b1e1358
        | (have j1 := b1e14 (σ x) (σ x)
           grind)
        | exact resolve b1e1358 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1358
      have b1e11171 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e11170
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e11170
        | exact resolve b1e11170 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11170
      have b1e11172 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
      clear b1e11171
      have b1e11185 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
        first
        | (have i₁ := b1e11172
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e11172
        | exact resolve b1e11172 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11172
      have b1e11192 : x = (k x (τ (σ x))) ∨ x = y := by
        first
        | (have i₁ := b1e1274 x
           have i₂ := b1e11185
           grind)
        | exact superpose b1e11185 b1e1274
        | exact resolve b1e1274 b1e11185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1274 b1e11185
      have b1e11237 : x = (k x x) ∨ x = y := by
        first
        | (have i₁ := b1e11192
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e11192
        | exact resolve b1e11192 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11192
      have b1e11239 : x = (k x x) := by
        first
        | (have r₁ := b1e11237
           have r₂ := b1e1327
           grind)
        | exact resolve b1e11237 b1e1327
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1327 b1e11237
      have b1e11260 : x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e14 x x
           have i₂ := b1e11239
           grind)
        | exact superpose b1e11239 b1e14
        | (have j0 := b1e14 x x
           grind)
        | exact resolve b1e14 b1e11239
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11239
      have b1e11261 : x = (M.op x x) := by grind
      clear b1e11260
      have b1e11289 : x = y := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e11261
           grind)
        | exact superpose b1e11261 b1e17
        | exact resolve b1e17 b1e11261
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11261
      have b1e11789 : (σ x) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e303
           have i₂ := b1e11289
           grind)
        | exact superpose b1e11289 b1e303
        | exact resolve b1e303 b1e11289
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e303
      have b1e11808 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e11789
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e11789
        | exact resolve b1e11789 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11789
      have b1e11813 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b1e11808
           have i₂ := b1e11289
           grind)
        | exact superpose b1e11289 b1e11808
        | exact resolve b1e11808 b1e11289
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11289 b1e11808
      have b1e11814 : False := by grind
      exact b1e11814
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
      have b2e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X2 X1 X3
           have i₂ := b2e10 X2 X1 X0
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e47 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b2e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
      have b2e53 : x = (M.op x y) ∨ y = (M.op x x) := by
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
      have b2e56 : x = (M.op x y) := by
        first
        | (have r₁ := b2e53
           have r₂ := b2e17
           grind)
        | exact resolve b2e53 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e53
      have b2e58 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b2e10 X0 y x
           have i₂ := b2e56
           grind)
        | exact superpose b2e56 b2e10
        | exact resolve b2e10 b2e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e92 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e33 X0 y X1 x
           have i₂ := b2e56
           grind)
        | exact superpose b2e56 b2e33
        | exact resolve b2e33 b2e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e33
      have b2e110 : (M.op x (M.op y y)) = (M.op (M.op y y) (M.op x y)) := by
        first
        | (have i₁ := b2e58 (M.op y y)
           have i₂ := b2e58 y
           grind)
        | exact superpose b2e58 b2e58
        | exact resolve b2e58 b2e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e117 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op X1 (M.op (M.op y X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X1 (M.op y X0) X0
           have i₂ := b2e58 X0
           grind)
        | exact superpose b2e58 b2e10
        | exact resolve b2e10 b2e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58
      have b2e121 : (M.op x (M.op y y)) = (M.op x (M.op x y)) := by
        first
        | (have i₁ := b2e110
           have i₂ := b2e92 y (M.op x y)
           grind)
        | exact superpose b2e92 b2e110
        | exact resolve b2e110 b2e92
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e110
      have b2e122 : (M.op x x) = (M.op x (M.op y y)) := by
        first
        | (have i₁ := b2e121
           have i₂ := b2e56
           grind)
        | exact superpose b2e56 b2e121
        | exact resolve b2e121 b2e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e121
      have b2e182 : ∀ X0 : G, (M.op (M.op x x) X0) = (M.op X0 (M.op (M.op y y) X0)) := by
        intro X0
        first
        | (have i₁ := b2e10 X0 (M.op y y) x
           have i₂ := b2e122
           grind)
        | exact superpose b2e122 b2e10
        | exact resolve b2e10 b2e122
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e122
      have b2e185 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x x) X0) := by
        intro X0
        first
        | (have i₁ := b2e182 X0
           have i₂ := b2e117 y X0
           grind)
        | exact superpose b2e117 b2e182
        | exact resolve b2e182 b2e117
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e117 b2e182
      have b2e189 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x x) X0) := by
        intro X0
        first
        | (have i₁ := b2e185 X0
           have i₂ := b2e92 x X0
           grind)
        | exact superpose b2e92 b2e185
        | exact resolve b2e185 b2e92
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e92 b2e185
      have b2e227 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b2e10 X0 x x
           have i₂ := b2e189 X0
           grind)
        | exact superpose b2e189 b2e10
        | exact resolve b2e10 b2e189
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e189
      have b2e370 : x = (M.op y x) := by
        first
        | (have i₁ := b2e227 y
           have i₂ := b2e56
           grind)
        | exact superpose b2e56 b2e227
        | exact resolve b2e227 b2e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e56 b2e227
      have b2e1560 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e51 x x
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e51
        | exact resolve b2e51 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e51
      have b2e2691 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e11 (k x x)
           have i₂ := b2e1560
           grind)
        | exact superpose b2e1560 b2e11
        | exact resolve b2e11 b2e1560
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1560
      have b2e2704 : y = (k x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e2691
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e2691
        | exact resolve b2e2691 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2691
      have b2e2711 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e47 x x
           have i₂ := b2e2704
           grind)
        | exact superpose b2e2704 b2e47
        | exact resolve b2e47 b2e2704
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47 b2e2704
      have b2e2714 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b2e2711
           have r₂ := b2e17
           grind)
        | exact resolve b2e2711 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2711
      have b2e3012 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b2e11 y
           have i₂ := b2e2714
           grind)
        | exact superpose b2e2714 b2e11
        | exact resolve b2e11 b2e2714
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2714
      have b2e3028 : x = y ∨ x = y := by
        first
        | (have i₁ := b2e3012
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e3012
        | exact resolve b2e3012 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3012
      have b2e3029 : x = y := by grind
      clear b2e3028
      have b2e3367 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e3029
           grind)
        | exact superpose b2e3029 b2e16
        | exact resolve b2e16 b2e3029
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e3378 : x = (M.op x x) := by
        first
        | (have i₁ := b2e370
           have i₂ := b2e3029
           grind)
        | exact superpose b2e3029 b2e370
        | exact resolve b2e370 b2e3029
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e370
      have b2e3385 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e3367
           have i₂ := b2e3378
           grind)
        | exact superpose b2e3378 b2e3367
        | exact resolve b2e3367 b2e3378
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3367 b2e3378
      have b2e3386 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e3385
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e3385
        | exact resolve b2e3385 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3385
      have b2e3387 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b2e3386
           have i₂ := b2e3029
           grind)
        | exact superpose b2e3029 b2e3386
        | exact resolve b2e3386 b2e3029
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3029 b2e3386
      have b2e3388 : False := by grind
      exact b2e3388
    · have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x x) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e38 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
      have b3e177 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b3e38 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e38
      have b3e178 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e177
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e177
        | exact resolve b3e177 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e177
      have b3e263 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e178
           grind)
        | exact superpose b3e178 b3e16
        | exact resolve b3e16 b3e178
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e178
      have b3e390 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b3e263
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e263
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e263 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e263
      have b3e391 : y = (M.op x x) := by grind
      clear b3e390
      have b3e393 : False := by grind
      exact b3e393

/-- `Equation4456`: `x ◇ (y ◇ x) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation4456 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4456 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4456.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
          intro X0 X1 X2
          grind
        have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e18 : y = (M.op x x) := by grind
        have b0e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b0e20 : y = (M.op y y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b0e23 : y = (k y y) := by grind
        have b0e40 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b0e11 X0 (σ x) (σ x)
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e11
          | exact resolve b0e11 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e41 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b0e11 X0 x x
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e11
          | exact resolve b0e11 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e43 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b0e41 x
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e41
          | exact resolve b0e41 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41
        have b0e61 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b0e207 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b0e40 (σ x)
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e40
          | exact resolve b0e40 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e40
        have b0e1701 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e61 x y
             grind)
          | exact superpose b0e61 b0e17
          | (have j1 := b0e61 x y
             grind)
          | exact resolve b0e17 b0e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e1758 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b0e61 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e61
        have b0e1774 : (σ (k y x)) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e1701
             have i₂ := b0e43
             grind)
          | exact superpose b0e43 b0e1701
          | exact resolve b0e1701 b0e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e1701
        have b0e1784 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e207
             grind)
          | exact superpose b0e207 b0e17
          | exact resolve b0e17 b0e207
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e207
        have b0e1813 : (M.op (σ y) (σ x)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b0e1784
             have i₂ := b0e43
             grind)
          | exact superpose b0e43 b0e1784
          | exact resolve b0e1784 b0e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e1784
        have b0e22149 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e1758 y
             have i₂ := b0e23
             grind)
          | exact superpose b0e23 b0e1758
          | (have j0 := b0e1758 y
             grind)
          | exact resolve b0e1758 b0e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e23 b0e1758
        have b0e22156 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b0e22149
        have b0e48357 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b0e1774
             have i₂ := b0e15 y x
             grind)
          | exact superpose b0e15 b0e1774
          | (have j1 := b0e15 (σ y) (σ x)
             grind)
          | exact resolve b0e1774 b0e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e1774
        have b0e48367 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b0e48357
             have i₂ := b0e43
             grind)
          | exact superpose b0e43 b0e48357
          | exact resolve b0e48357 b0e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e43 b0e48357
        have b0e48368 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
        clear b0e48367
        have b0e48380 : (σ x) = (σ y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b0e48368
             have i₂ := b0e22156
             grind)
          | exact superpose b0e22156 b0e48368
          | exact resolve b0e48368 b0e22156
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e48368
        have b0e48385 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b0e48380
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e48380
          | exact resolve b0e48380 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e48380
        have b0e48414 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b0e12 x
             have i₂ := b0e48385
             grind)
          | exact superpose b0e48385 b0e12
          | exact resolve b0e12 b0e48385
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e48385
        have b0e48451 : x = y ∨ x = y := by
          first
          | (have i₁ := b0e48414
             have i₂ := b0e12 y
             grind)
          | exact superpose b0e12 b0e48414
          | exact resolve b0e48414 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e48414
        have b0e48452 : x = y := by grind
        clear b0e48451
        have b0e50174 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b0e1813
             have i₂ := b0e48452
             grind)
          | exact superpose b0e48452 b0e1813
          | exact resolve b0e1813 b0e48452
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e1813 b0e48452
        have b0e50191 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e50174
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e50174
          | exact resolve b0e50174 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e50174
        have b0e50197 : False := by grind
        exact b0e50197
      · have b1e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
          intro X0 X1 X2
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
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e18 : y = (M.op x x) := by grind
        have b1e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b1e20 : y ≠ (M.op y y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
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
        have b1e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11 X2 X1 X3
             have i₂ := b1e11 X2 X1 X0
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11 X3 (M.op X1 X2) X2
             have i₂ := b1e11 X2 X1 X0
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e11 X0 x x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e11
          | exact resolve b1e11 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b1e34 x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e34
          | exact resolve b1e34 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 X0 x X1
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e11
          | exact resolve b1e11 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e47 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b1e54 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op (M.op y x) X0) := by
          intro X0
          first
          | (have i₁ := b1e11 X0 y x
             have i₂ := b1e35
             grind)
          | exact superpose b1e35 b1e11
          | exact resolve b1e11 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e54 X0
             have i₂ := b1e38 X0 y
             grind)
          | exact superpose b1e38 b1e54
          | exact resolve b1e54 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38 b1e54
        have b1e83 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (k X0 (τ X1))
             have i₂ := b1e26 X1 X0
             grind)
          | exact superpose b1e26 b1e12
          | exact resolve b1e12 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e118 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e30 X0 (σ x) X1 (σ x)
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e30
          | exact resolve b1e30 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e439 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b1e83
        have b1e453 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e439 X0
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e439
          | exact resolve b1e439 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e439
        have b1e705 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ x)) (σ x)) X0) = (M.op X0 (M.op (σ y) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e31 X1 (σ x) (σ x) X0
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e31
          | exact resolve b1e31 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e868 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b1e705 X0 x
             have i₂ := b1e118 (M.op x (σ x)) X0
             grind)
          | exact superpose b1e118 b1e705
          | exact resolve b1e705 b1e118
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e118 b1e705
        have b1e1645 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e17
             have i₂ := b1e52 x y
             grind)
          | exact superpose b1e52 b1e17
          | (have j1 := b1e52 x y
             grind)
          | exact resolve b1e17 b1e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e1715 : (σ (k y x)) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e1645
             have i₂ := b1e35
             grind)
          | exact superpose b1e35 b1e1645
          | exact resolve b1e1645 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1645
        have b1e45498 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e1715
             have i₂ := b1e15 y x
             grind)
          | exact superpose b1e15 b1e1715
          | (have j1 := b1e15 (σ y) (σ x)
             grind)
          | exact resolve b1e1715 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e45501 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e1715
             have i₂ := b1e47 x y
             grind)
          | exact superpose b1e47 b1e1715
          | (have j1 := b1e47 x y
             grind)
          | exact resolve b1e1715 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47 b1e1715
        have b1e45502 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e45501
             have i₂ := b1e35
             grind)
          | exact superpose b1e35 b1e45501
          | exact resolve b1e45501 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45501
        have b1e45503 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by grind
        clear b1e45502
        have b1e45508 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e45498
             have i₂ := b1e35
             grind)
          | exact superpose b1e35 b1e45498
          | exact resolve b1e45498 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45498
        have b1e45509 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
        clear b1e45508
        have b1e45522 : y = (k y (τ (σ x))) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e453 y
             have i₂ := b1e45503
             grind)
          | exact superpose b1e45503 b1e453
          | exact resolve b1e453 b1e45503
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e453 b1e45503
        have b1e45642 : y = (k y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e45522
             have i₂ := b1e12 x
             grind)
          | exact superpose b1e12 b1e45522
          | exact resolve b1e45522 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45522
        have b1e45643 : y = (k y x) := by grind
        clear b1e45642
        have b1e47106 : y = (M.op x y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e15 y x
             have i₂ := b1e45643
             grind)
          | exact superpose b1e45643 b1e15
          | (have j0 := b1e15 y x
             grind)
          | exact resolve b1e15 b1e45643
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45643
        have b1e47111 : y = (M.op y x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e47106
             have i₂ := b1e35
             grind)
          | exact superpose b1e35 b1e47106
          | exact resolve b1e47106 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35 b1e47106
        have b1e50893 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e868 (σ y)
             have i₂ := b1e45509
             grind)
          | exact superpose b1e45509 b1e868
          | exact resolve b1e868 b1e45509
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45509
        have b1e52991 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e868 (σ x)
             have i₂ := b1e50893
             grind)
          | exact superpose b1e50893 b1e868
          | exact resolve b1e868 b1e50893
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e868 b1e50893
        have b1e53099 : x = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e52991
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e52991
          | exact resolve b1e52991 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52991
        have b1e54258 : x ≠ y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e53099
             grind)
          | exact superpose b1e53099 b1e20
          | exact resolve b1e20 b1e53099
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e54272 : x = (M.op y x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e55 y
             have i₂ := b1e53099
             grind)
          | exact superpose b1e53099 b1e55
          | exact resolve b1e55 b1e53099
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53099
        have b1e56670 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e55 x
             have i₂ := b1e54272
             grind)
          | exact superpose b1e54272 b1e55
          | exact resolve b1e55 b1e54272
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e54272
        have b1e56780 : x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e56670
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e56670
          | exact resolve b1e56670 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56670
        have b1e56793 : (σ x) = (σ y) := by
          first
          | (have r₁ := b1e56780
             have r₂ := b1e54258
             grind)
          | exact resolve b1e56780 b1e54258
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54258 b1e56780
        have b1e57130 : x = (τ (σ y)) := by
          first
          | (have i₁ := b1e12 x
             have i₂ := b1e56793
             grind)
          | exact superpose b1e56793 b1e12
          | exact resolve b1e12 b1e56793
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56793
        have b1e57166 : x = y := by
          first
          | (have i₁ := b1e57130
             have i₂ := b1e12 y
             grind)
          | exact superpose b1e12 b1e57130
          | exact resolve b1e57130 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57130
        have b1e59730 : y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e47111
             have i₂ := b1e57166
             grind)
          | exact superpose b1e57166 b1e47111
          | exact resolve b1e47111 b1e57166
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47111 b1e57166
        have b1e59732 : y = (M.op y y) := by grind
        clear b1e59730
        have b1e59735 : False := by grind
        exact b1e59735
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b2e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e18 : y = (M.op x x) := by grind
        have b2e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e20 : y = (M.op y y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b2e23 : y = (k y y) := by grind
        have b2e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X1 (τ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e16
          | exact resolve b2e16 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b2e92 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (k X0 (τ X1))
             have i₂ := b2e25 X1 X0
             grind)
          | exact superpose b2e25 b2e12
          | exact resolve b2e12 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e207 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e52 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e484 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e92
        have b2e498 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e484 X0
             have i₂ := b2e12 X0
             grind)
          | exact superpose b2e12 b2e484
          | exact resolve b2e484 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e484
        have b2e683 : x ≠ y ∨ x = (k x x) := by
          first
          | (have i₁ := b2e207 x x
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e207
          | (have j0 := b2e207 x x
             grind)
          | exact resolve b2e207 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e207
        have b2e1365 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e56 x x
             grind)
          | exact superpose b2e56 b2e19
          | (have j1 := b2e56 x x
             grind)
          | (have r₁ := b2e19
             have r₂ := b2e56 y x
             grind)
          | exact resolve b2e19 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1414 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e56 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e13431 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e1365
             have i₂ := b2e15 x x
             grind)
          | exact superpose b2e15 b2e1365
          | (have j1 := b2e15 (σ x) (σ x)
             grind)
          | exact resolve b2e1365 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1365
        have b2e13432 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e13431
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e13431
          | exact resolve b2e13431 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13431
        have b2e13433 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e13432
        have b2e13446 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e13433
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e13433
          | exact resolve b2e13433 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13433
        have b2e13454 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e498 x
             have i₂ := b2e13446
             grind)
          | exact superpose b2e13446 b2e498
          | exact resolve b2e498 b2e13446
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e498 b2e13446
        have b2e13506 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e13454
             have i₂ := b2e12 x
             grind)
          | exact superpose b2e12 b2e13454
          | exact resolve b2e13454 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13454
        have b2e13508 : x = (k x x) := by
          first
          | (have r₁ := b2e13506
             have r₂ := b2e683
             grind)
          | exact resolve b2e13506 b2e683
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e683 b2e13506
        have b2e13530 : x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e15 x x
             have i₂ := b2e13508
             grind)
          | exact superpose b2e13508 b2e15
          | (have j0 := b2e15 x x
             grind)
          | exact resolve b2e15 b2e13508
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13508
        have b2e13531 : x = (M.op x x) := by grind
        clear b2e13530
        have b2e13533 : x = y := by
          first
          | (have i₁ := b2e13531
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e13531
          | exact resolve b2e13531 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13531
        have b2e13558 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e1414 y
             have i₂ := b2e23
             grind)
          | exact superpose b2e23 b2e1414
          | (have j0 := b2e1414 y
             grind)
          | exact resolve b2e1414 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e1414
        have b2e13564 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e13558
        have b2e13577 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e13533
             grind)
          | exact superpose b2e13533 b2e19
          | exact resolve b2e19 b2e13533
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13533
        have b2e13610 : False := by grind
        exact b2e13610
      · have b3e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e18 : y = (M.op x x) := by grind
        have b3e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
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
        have b3e42 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b3e78 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b3e169 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e42 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e842 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b3e78
        have b3e857 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e842 X0
             have i₂ := b3e12 X0
             grind)
          | exact superpose b3e12 b3e842
          | exact resolve b3e842 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e842
        have b3e1070 : x ≠ y ∨ x = (k x x) := by
          first
          | (have i₁ := b3e169 x x
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e169
          | (have j0 := b3e169 x x
             grind)
          | exact resolve b3e169 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e169
        have b3e1378 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e47 x x
             grind)
          | exact superpose b3e47 b3e19
          | (have j1 := b3e47 x x
             grind)
          | (have r₁ := b3e19
             have r₂ := b3e47 y x
             grind)
          | exact resolve b3e19 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1427 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b3e47 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e10481 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e1378
             have i₂ := b3e15 x x
             grind)
          | exact superpose b3e15 b3e1378
          | (have j1 := b3e15 (σ x) (σ x)
             grind)
          | exact resolve b3e1378 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1378
        have b3e10482 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e10481
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e10481
          | exact resolve b3e10481 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10481
        have b3e10483 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b3e10482
        have b3e10494 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b3e10483
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e10483
          | exact resolve b3e10483 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10483
        have b3e10500 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b3e857 x
             have i₂ := b3e10494
             grind)
          | exact superpose b3e10494 b3e857
          | exact resolve b3e857 b3e10494
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e857 b3e10494
        have b3e10547 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b3e10500
             have i₂ := b3e12 x
             grind)
          | exact superpose b3e12 b3e10500
          | exact resolve b3e10500 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10500
        have b3e10549 : x = (k x x) := by
          first
          | (have r₁ := b3e10547
             have r₂ := b3e1070
             grind)
          | exact resolve b3e10547 b3e1070
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1070 b3e10547
        have b3e10569 : x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e15 x x
             have i₂ := b3e10549
             grind)
          | exact superpose b3e10549 b3e15
          | (have j0 := b3e15 x x
             grind)
          | exact resolve b3e15 b3e10549
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e10570 : x = (M.op x x) := by grind
        clear b3e10569
        have b3e10572 : x = y := by
          first
          | (have i₁ := b3e10570
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e10570
          | exact resolve b3e10570 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10570
        have b3e10593 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e1427 x
             have i₂ := b3e10549
             grind)
          | exact superpose b3e10549 b3e1427
          | (have j0 := b3e1427 x
             grind)
          | exact resolve b3e1427 b3e10549
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1427 b3e10549
        have b3e10599 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b3e10593
        have b3e10604 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e10599
             have i₂ := b3e10572
             grind)
          | exact superpose b3e10572 b3e10599
          | exact resolve b3e10599 b3e10572
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10599
        have b3e10612 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e10572
             grind)
          | exact superpose b3e10572 b3e19
          | exact resolve b3e19 b3e10572
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10572
        have b3e10645 : False := by grind
        exact b3e10645
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b4e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
          intro X0 X1 X2
          grind
        have b4e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b4e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b4e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b4e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b4e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b4e18 : y ≠ (M.op x x) := by grind
        have b4e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b4e20 : y = (M.op y y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b4e23 : (σ x) = (k (σ x) (σ y)) := by grind
        have b4e24 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b4e23
             have i₂ := b4e16 x y
             grind)
          | exact superpose b4e16 b4e23
          | exact resolve b4e23 b4e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e23
        have b4e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b4e29 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b4e12 (k x y)
             have i₂ := b4e24
             grind)
          | exact superpose b4e24 b4e12
          | exact resolve b4e12 b4e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e24
        have b4e30 : x = (k x y) := by
          first
          | (have i₁ := b4e29
             have i₂ := b4e12 x
             grind)
          | exact superpose b4e12 b4e29
          | exact resolve b4e29 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e29
        have b4e40 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b4e11 X0 y y
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e11
          | exact resolve b4e11 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e56 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ y) = X0 := by
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
        have b4e58 : x = (M.op y x) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b4e30
             have i₂ := b4e15 x y
             grind)
          | exact superpose b4e15 b4e30
          | (have j1 := b4e15 x y
             grind)
          | exact resolve b4e30 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e30
        have b4e64 : x = (M.op y x) := by
          first
          | (have r₁ := b4e58
             have r₂ := b4e18
             grind)
          | exact resolve b4e58 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e58
        have b4e66 : x = (M.op x x) := by
          first
          | (have i₁ := b4e40 x
             have i₂ := b4e64
             grind)
          | exact superpose b4e64 b4e40
          | exact resolve b4e40 b4e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e40 b4e64
        have b4e69 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
          intro X0
          grind
        clear b4e25
        have b4e74 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b4e69 X0
             have i₂ := b4e13 X0
             grind)
          | exact superpose b4e13 b4e69
          | exact resolve b4e69 b4e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e69
        have b4e75 : x ≠ y := by
          first
          | (have i₁ := b4e18
             have i₂ := b4e66
             grind)
          | exact superpose b4e66 b4e18
          | exact resolve b4e18 b4e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e564 : (σ x) = (M.op (σ (M.op (τ (σ x)) (τ (σ x)))) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e56 (σ (M.op (τ (σ x)) (τ (σ x))))
             have i₂ := b4e74 (σ x)
             grind)
          | exact superpose b4e74 b4e56
          | (have j0 := b4e56 (σ (M.op (τ (σ x)) (τ (σ x))))
             grind)
          | exact resolve b4e56 b4e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e56 b4e74
        have b4e567 : (σ x) = (M.op (σ (M.op x x)) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e564
             have i₂ := b4e12 x
             grind)
          | exact superpose b4e12 b4e564
          | exact resolve b4e564 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e564
        have b4e573 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e567
             have i₂ := b4e66
             grind)
          | exact superpose b4e66 b4e567
          | exact resolve b4e567 b4e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e567
        have b4e576 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e573
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e573
          | exact resolve b4e573 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e573
        have b4e578 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b4e576
             have i₂ := b4e12 x
             grind)
          | exact superpose b4e12 b4e576
          | exact resolve b4e576 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e576
        have b4e580 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b4e578
             have i₂ := b4e66
             grind)
          | exact superpose b4e66 b4e578
          | exact resolve b4e578 b4e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e66 b4e578
        have b4e581 : (σ x) = (σ y) := by grind
        clear b4e580
        have b4e779 : x = (τ (σ y)) := by
          first
          | (have i₁ := b4e12 x
             have i₂ := b4e581
             grind)
          | exact superpose b4e581 b4e12
          | exact resolve b4e12 b4e581
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e581
        have b4e780 : x = y := by
          first
          | (have i₁ := b4e779
             have i₂ := b4e12 y
             grind)
          | exact superpose b4e12 b4e779
          | exact resolve b4e779 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e779
        have b4e785 : False := by grind
        exact b4e785
      · have b5e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b5e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b5e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b5e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b5e18 : y ≠ (M.op x x) := by grind
        have b5e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b5e20 : y ≠ (M.op y y) := by grind
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
        clear b5e23
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
        have b5e57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b5e62 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b5e64 : x = (M.op y x) ∨ y = (M.op x x) := by
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
        have b5e67 : x = (M.op y x) := by
          first
          | (have r₁ := b5e64
             have r₂ := b5e18
             grind)
          | exact resolve b5e64 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e64
        have b5e1410 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e62 x x
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e62
          | exact resolve b5e62 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e62
        have b5e1789 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e12 (k x x)
             have i₂ := b5e1410
             grind)
          | exact superpose b5e1410 b5e12
          | exact resolve b5e12 b5e1410
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1410
        have b5e1802 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e1789
             have i₂ := b5e12 y
             grind)
          | exact superpose b5e12 b5e1789
          | exact resolve b5e1789 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1789
        have b5e1809 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e57 x x
             have i₂ := b5e1802
             grind)
          | exact superpose b5e1802 b5e57
          | exact resolve b5e57 b5e1802
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e57 b5e1802
        have b5e1812 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have r₁ := b5e1809
             have r₂ := b5e18
             grind)
          | exact resolve b5e1809 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1809
        have b5e2065 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b5e12 x
             have i₂ := b5e1812
             grind)
          | exact superpose b5e1812 b5e12
          | exact resolve b5e12 b5e1812
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1812
        have b5e2078 : x = y ∨ x = y := by
          first
          | (have i₁ := b5e2065
             have i₂ := b5e12 y
             grind)
          | exact superpose b5e12 b5e2065
          | exact resolve b5e2065 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e2065
        have b5e2079 : x = y := by grind
        clear b5e2078
        have b5e2331 : y = (M.op y y) := by
          first
          | (have i₁ := b5e67
             have i₂ := b5e2079
             grind)
          | exact superpose b5e2079 b5e67
          | exact resolve b5e67 b5e2079
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e67 b5e2079
        have b5e2337 : False := by grind
        exact b5e2337
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b6e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b6e20 : y = (M.op y y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b6e22 : y = (k y y) := by grind
        have b6e46 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b6e1332 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e17
             have i₂ := b6e46 x y
             grind)
          | exact superpose b6e46 b6e17
          | (have j1 := b6e46 x y
             grind)
          | exact resolve b6e17 b6e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1383 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e46 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46
        have b6e10908 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e1383 y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1383
          | (have j0 := b6e1383 y
             grind)
          | exact resolve b6e1383 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e22 b6e1383
        have b6e10914 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b6e10908
        have b6e28374 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e1332
             have i₂ := b6e15 y x
             grind)
          | exact superpose b6e15 b6e1332
          | (have j1 := b6e15 (σ y) (σ x)
             grind)
          | exact resolve b6e1332 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1332
        have b6e28381 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
        clear b6e28374
        have b6e28388 : (σ x) = (σ y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e28381
             have i₂ := b6e10914
             grind)
          | exact superpose b6e10914 b6e28381
          | exact resolve b6e28381 b6e10914
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28381
        have b6e28392 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b6e28388
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e28388
          | exact resolve b6e28388 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28388
        have b6e28402 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b6e12 x
             have i₂ := b6e28392
             grind)
          | exact superpose b6e28392 b6e12
          | exact resolve b6e12 b6e28392
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28392
        have b6e28441 : x = y ∨ x = y := by
          first
          | (have i₁ := b6e28402
             have i₂ := b6e12 y
             grind)
          | exact superpose b6e12 b6e28402
          | exact resolve b6e28402 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28402
        have b6e28442 : x = y := by grind
        clear b6e28441
        have b6e28538 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e28442
             grind)
          | exact superpose b6e28442 b6e19
          | exact resolve b6e19 b6e28442
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28442
        have b6e28561 : False := by grind
        exact b6e28561
      · have b7e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
          intro X0 X1 X2
          grind
        have b7e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b7e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b7e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b7e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b7e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b7e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b7e18 : y ≠ (M.op x x) := by grind
        have b7e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b7e20 : y ≠ (M.op y y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b7e22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b7e23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e16 X1 (τ X0)
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e16
          | exact resolve b7e16 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e25 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
          intro X0
          grind
        have b7e28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b7e12 (k (τ X0) X1)
             have i₂ := b7e22 X0 X1
             grind)
          | exact superpose b7e22 b7e12
          | exact resolve b7e12 b7e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e29 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b7e25 X0
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e25
          | exact resolve b7e25 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e25
        have b7e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e11 X0 (M.op X2 X1) X3
             have i₂ := b7e11 X0 X1 X2
             grind)
          | exact superpose b7e11 b7e11
          | exact resolve b7e11 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e11 X2 X1 X3
             have i₂ := b7e11 X2 X1 X0
             grind)
          | exact superpose b7e11 b7e11
          | exact resolve b7e11 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e11 X3 (M.op X1 X2) X2
             have i₂ := b7e11 X2 X1 X0
             grind)
          | exact superpose b7e11 b7e11
          | exact resolve b7e11 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e34 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e11 X2 X0 (M.op x X1)
             have i₂ := b7e11 X0 X1 x
             grind)
          | exact superpose b7e11 b7e11
          | exact resolve b7e11 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e12 (k X0 (τ X1))
             have i₂ := b7e23 X1 X0
             grind)
          | exact superpose b7e23 b7e12
          | exact resolve b7e12 b7e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e45 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b7e48 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
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
        have b7e49 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b7e23 X0 X1
             have i₂ := b7e15 X1 (τ X0)
             grind)
          | exact superpose b7e15 b7e23
          | (have j1 := b7e15 X1 (τ X0)
             grind)
          | exact resolve b7e23 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e50 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b7e52 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
        have b7e75 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X3) = (M.op (M.op X2 X0) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e32 X2 X0 X3 (M.op x X1)
             have i₂ := b7e11 X0 X1 x
             grind)
          | exact superpose b7e11 b7e32
          | exact resolve b7e32 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e95 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e29 X1
             have i₂ := b7e15 (τ X1) X0
             grind)
          | (have i₁ := b7e29 X0
             have i₂ := b7e15 X0 (M.op (τ X0) (τ X0))
             grind)
          | exact superpose b7e15 b7e29
          | (have j1 := b7e15 (τ X1) X0
             grind)
          | exact resolve b7e29 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e29
        have b7e115 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b7e45 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e45
        have b7e121 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b7e40
        have b7e135 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b7e121 X0
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e121
          | exact resolve b7e121 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e121
        have b7e184 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b7e48 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e48
        have b7e185 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b7e184
             have i₂ := b7e16 x y
             grind)
          | exact superpose b7e16 b7e184
          | exact resolve b7e184 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e184
        have b7e233 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b7e34 X1 x X0
             have i₂ := b7e31 X0 X1 x X1
             grind)
          | exact superpose b7e31 b7e34
          | exact resolve b7e34 b7e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e34
        have b7e360 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (M.op (M.op X1 X2) X3) = (k (M.op (M.op X1 X2) X3) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e115 (M.op (M.op X1 X2) X3) X3
             have i₂ := b7e33 X0 X1 X2 X3
             grind)
          | exact superpose b7e33 b7e115
          | (have j0 := b7e115 (M.op (M.op X1 X2) X3) X3
             grind)
          | exact resolve b7e115 b7e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e33 b7e115
        have b7e384 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (k (M.op (M.op X1 X2) X3) X3) := by
          intro X1 X2 X3
          first
          | (have j0 := b7e360 x X1 X2 X3
             grind)
          | (have r₁ := b7e360 x x X1 X2
             have r₂ := b7e32 x X1 X2 (M.op x x)
             grind)
          | (have r₁ := b7e360 x X3 X1 X2
             have r₂ := b7e32 (M.op x X3) X1 X2 X3
             grind)
          | exact resolve b7e360 b7e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e360
        have b7e408 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e135 X1
             have i₂ := b7e15 (σ X1) X0
             grind)
          | (have i₁ := b7e135 X0
             have i₂ := b7e15 X0 (M.op (σ X0) (σ X0))
             grind)
          | exact superpose b7e15 b7e135
          | (have j1 := b7e15 (σ X1) X0
             grind)
          | exact resolve b7e135 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e593 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op X2 (M.op X1 X2))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e31 X2 X1 x X1
             have i₂ := b7e75 X1 x X0 X2
             grind)
          | exact superpose b7e75 b7e31
          | exact resolve b7e31 b7e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e31 b7e75
        have b7e1402 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b7e50 X0 X0
             have i₂ := b7e15 (σ X0) X1
             grind)
          | (have i₁ := b7e50 X0 X1
             have i₂ := b7e15 X0 (M.op (σ X0) (σ X1))
             grind)
          | exact superpose b7e15 b7e50
          | (have j1 := b7e15 (σ X1) X0
             grind)
          | exact resolve b7e50 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e1417 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e50 x y
             grind)
          | exact superpose b7e50 b7e17
          | (have j1 := b7e50 x y
             grind)
          | exact resolve b7e17 b7e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e1420 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b7e1445 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b7e12 X1
             have i₂ := b7e50 X1 X0
             grind)
          | exact superpose b7e50 b7e12
          | (have j1 := b7e50 X1 X0
             grind)
          | exact resolve b7e12 b7e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e1456 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e135 X1
             have i₂ := b7e50 X0 X1
             grind)
          | exact superpose b7e50 b7e135
          | (have j1 := b7e50 X0 X1
             grind)
          | exact resolve b7e135 b7e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e1479 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b7e50 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e50
        have b7e1483 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e1456 X0 X1
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e1456
          | (have j0 := b7e1456 X0 X1
             grind)
          | exact resolve b7e1456 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1456
        have b7e1490 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b7e1420 X0
             have i₂ := b7e16 X0 (k X0 X0)
             grind)
          | exact superpose b7e16 b7e1420
          | (have j0 := b7e1420 X0
             grind)
          | exact resolve b7e1420 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1420
        have b7e7806 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b7e1479 (τ X0)
             have i₂ := b7e23 X0 (τ X0)
             grind)
          | exact superpose b7e23 b7e1479
          | (have j0 := b7e1479 (τ X0)
             grind)
          | exact resolve b7e1479 b7e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1479
        have b7e7808 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b7e7806 X0
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e7806
          | (have j0 := b7e7806 X0
             grind)
          | exact resolve b7e7806 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e7806
        have b7e7811 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b7e7808 X0
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e7808
          | (have j0 := b7e7808 X0
             grind)
          | exact resolve b7e7808 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e7808
        have b7e7824 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e49 (σ X0) X1
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e49
          | exact resolve b7e49 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e7873 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b7e13 X1
             have i₂ := b7e49 X1 X0
             grind)
          | exact superpose b7e49 b7e13
          | (have j1 := b7e49 X1 X0
             grind)
          | exact resolve b7e13 b7e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e49
        have b7e8004 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b7e7824 X0 X1
             have i₂ := b7e16 X1 X0
             grind)
          | exact superpose b7e16 b7e7824
          | (have j0 := b7e7824 X0 X1
             grind)
          | exact resolve b7e7824 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e7824
        have b7e8027 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b7e7811 (τ X0)
             have i₂ := b7e52 X0 X0
             grind)
          | exact superpose b7e52 b7e7811
          | (have j0 := b7e7811 (τ X0)
             grind)
          | exact resolve b7e7811 b7e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e7811
        have b7e8646 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b7e14730 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e95 X0 (σ X0)
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e95
          | (have j0 := b7e95 X1 (σ X0)
             grind)
          | exact resolve b7e95 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e95
        have b7e14791 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b7e14730 X0 X1
             have i₂ := b7e16 X0 X1
             grind)
          | exact superpose b7e16 b7e14730
          | (have j0 := b7e14730 X0 X1
             grind)
          | exact resolve b7e14730 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e14730
        have b7e18086 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
          first
          | (have i₁ := b7e1417
             have i₂ := b7e8646 x y
             grind)
          | exact superpose b7e8646 b7e1417
          | (have j1 := b7e8646 x y
             grind)
          | (have r₁ := b7e1417
             have r₂ := b7e8646 x y
             grind)
          | exact resolve b7e1417 b7e8646
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e8646
        have b7e18087 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e1417
             have i₂ := b7e8004 x y
             grind)
          | exact superpose b7e8004 b7e1417
          | (have j1 := b7e8004 (σ x) (σ y)
             grind)
          | (have r₁ := b7e1417
             have r₂ := b7e8004 x y
             grind)
          | exact resolve b7e1417 b7e8004
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e18088 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
        clear b7e18087
        have b7e18089 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by grind
        clear b7e18086
        have b7e18223 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b7e22 X0 (k (τ X0) (τ X0))
             have i₂ := b7e1490 (τ X0)
             grind)
          | exact superpose b7e1490 b7e22
          | (have j1 := b7e1490 (τ X0)
             grind)
          | exact resolve b7e22 b7e1490
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1490
        have b7e18263 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b7e18223 X0
             have i₂ := b7e23 X0 (τ X0)
             grind)
          | exact superpose b7e23 b7e18223
          | (have j0 := b7e18223 X0
             grind)
          | exact resolve b7e18223 b7e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e18223
        have b7e18271 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b7e18263 X0
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e18263
          | (have j0 := b7e18263 X0
             grind)
          | exact resolve b7e18263 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e18263
        have b7e18276 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b7e18271 X0
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e18271
          | (have j0 := b7e18271 X0
             grind)
          | exact resolve b7e18271 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e18271
        have b7e20986 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e1445 (τ X0) X1
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e1445
          | exact resolve b7e1445 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1445
        have b7e21125 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e20986 X0 X1
             have i₂ := b7e22 X0 X1
             grind)
          | exact superpose b7e22 b7e20986
          | (have j0 := b7e20986 X0 X1
             grind)
          | exact resolve b7e20986 b7e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e22 b7e20986
        have b7e22164 : y = (k y (τ (σ x))) ∨ y = (k y x) := by
          first
          | (have i₁ := b7e135 y
             have i₂ := b7e18089
             grind)
          | exact superpose b7e18089 b7e135
          | exact resolve b7e135 b7e18089
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e135 b7e18089
        have b7e22266 : y = (k y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b7e22164
             have i₂ := b7e12 x
             grind)
          | exact superpose b7e12 b7e22164
          | exact resolve b7e22164 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e22164
        have b7e22267 : y = (k y x) := by grind
        clear b7e22266
        have b7e23534 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b7e1417
             have i₂ := b7e22267
             grind)
          | exact superpose b7e22267 b7e1417
          | exact resolve b7e1417 b7e22267
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1417 b7e22267
        have b7e42846 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e1402 X0 (τ X0)
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e1402
          | (have j0 := b7e1402 X1 (τ X0)
             grind)
          | exact resolve b7e1402 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1402
        have b7e42977 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e42846 X0 X1
             have i₂ := b7e23 X0 (τ X0)
             grind)
          | exact superpose b7e23 b7e42846
          | (have j0 := b7e42846 X0 X1
             grind)
          | exact resolve b7e42846 b7e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e23 b7e42846
        have b7e42988 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e42977 X0 X1
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e42977
          | (have j0 := b7e42977 X0 X1
             grind)
          | exact resolve b7e42977 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e42977
        have b7e64752 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e21125 X0 (τ X0)
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e21125
          | (have j0 := b7e21125 X1 (τ X0)
             grind)
          | exact resolve b7e21125 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e21125
        have b7e71626 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (τ X0) = (k (τ X0) (τ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e408 X0 (τ X0)
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e408
          | (have j0 := b7e408 X1 (τ X0)
             grind)
          | exact resolve b7e408 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e71678 : ∀ X0 X1 : G, (k (τ (σ X1)) X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 (τ (σ X0))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e28 (σ X1) X0
             have i₂ := b7e408 (σ X0) X1
             grind)
          | exact superpose b7e408 b7e28
          | (have j1 := b7e408 (σ X0) X1
             grind)
          | exact resolve b7e28 b7e408
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e28 b7e408
        have b7e71708 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 (τ (σ X0))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e71678 X0 X1
             have i₂ := b7e12 X1
             grind)
          | exact superpose b7e12 b7e71678
          | (have j0 := b7e71678 X0 X1
             grind)
          | exact resolve b7e71678 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e71678
        have b7e71730 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b7e71626 X0 X1
             have i₂ := b7e52 X1 X0
             grind)
          | exact superpose b7e52 b7e71626
          | (have j0 := b7e71626 X0 X1
             grind)
          | exact resolve b7e71626 b7e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e52 b7e71626
        have b7e71744 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e71708 X0 X1
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e71708
          | (have j0 := b7e71708 X0 X1
             grind)
          | exact resolve b7e71708 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e71708
        have b7e76234 : (σ y) ≠ (σ (k x x)) ∨ x = (k x x) := by
          first
          | (have i₁ := b7e19
             have i₂ := b7e1483 x x
             grind)
          | exact superpose b7e1483 b7e19
          | (have j1 := b7e1483 x x
             grind)
          | exact resolve b7e19 b7e1483
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e76262 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X0) X2)) = (M.op (σ (k X0 X1)) X2) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e11 X2 (σ X0) (σ X1)
             have i₂ := b7e1483 X1 X0
             grind)
          | exact superpose b7e1483 b7e11
          | (have j1 := b7e1483 X1 X0
             grind)
          | exact resolve b7e11 b7e1483
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1483
        have b7e78296 : ∀ X0 : G, (σ X0) ≠ (σ y) ∨ x = X0 ∨ (M.op X0 x) = (k x X0) ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b7e76234
             have i₂ := b7e42988 x x
             grind)
          | (have i₁ := b7e76234
             have i₂ := b7e42988 X0 (k x x)
             grind)
          | exact superpose b7e42988 b7e76234
          | (have j1 := b7e42988 x X0
             grind)
          | (have r₁ := b7e76234
             have r₂ := b7e42988 (σ y) (σ (k x x))
             grind)
          | (have r₁ := b7e76234
             have r₂ := b7e42988 (σ (k x x)) (σ y)
             grind)
          | exact resolve b7e76234 b7e42988
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e42988 b7e76234
        have b7e78308 : ∀ X0 : G, (σ X0) ≠ (σ y) ∨ x = X0 ∨ (M.op X0 x) = (k x X0) := by
          intro X0
          first
          | (have j0 := b7e78296 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e78296
        have b7e94089 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b7e8027 X0
             have i₂ := b7e71730 X0 X0
             grind)
          | exact superpose b7e71730 b7e8027
          | (have j0 := b7e8027 X0
             have j1 := b7e71730 X0 X0
             grind)
          | (have r₁ := b7e8027 x
             have r₂ := b7e71730 x x
             grind)
          | exact resolve b7e8027 b7e71730
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e8027 b7e71730
        have b7e94092 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b7e94089 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e94089
        have b7e174352 : (k y y) = (τ (σ x)) ∨ y = (k y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e71744 y y
             have i₂ := b7e18088
             grind)
          | exact superpose b7e18088 b7e71744
          | (have j0 := b7e71744 y y
             grind)
          | exact resolve b7e71744 b7e18088
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e18088 b7e71744
        have b7e174382 : x = (k y y) ∨ y = (k y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e174352
             have i₂ := b7e12 x
             grind)
          | exact superpose b7e12 b7e174352
          | exact resolve b7e174352 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e174352
        have b7e183237 : ∀ X0 : G, (σ y) ≠ X0 ∨ (τ X0) = x ∨ (k x (τ X0)) = (M.op (τ X0) x) := by
          intro X0
          first
          | (have i₁ := b7e78308 (τ X0)
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e78308
          | (have j0 := b7e78308 (τ X0)
             grind)
          | (have r₁ := b7e78308 (τ (σ y))
             have r₂ := b7e13 (σ y)
             grind)
          | exact resolve b7e78308 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e78308
        have b7e185239 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b7e94092 (σ X0)
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e94092
          | (have j0 := b7e94092 (σ X0)
             grind)
          | exact resolve b7e94092 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e94092
        have b7e185299 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b7e185239 X0
             have i₂ := b7e16 X0 X0
             grind)
          | exact superpose b7e16 b7e185239
          | (have j0 := b7e185239 X0
             grind)
          | exact resolve b7e185239 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e185239
        have b7e192036 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b7e174382
             have i₂ := b7e15 y y
             grind)
          | exact superpose b7e15 b7e174382
          | (have j1 := b7e15 y x
             grind)
          | exact resolve b7e174382 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e174382
        have b7e192059 : x = (M.op y y) ∨ y = (M.op y y) := by grind
        clear b7e192036
        have b7e192066 : x = (M.op y y) := by
          first
          | (have r₁ := b7e192059
             have r₂ := b7e20
             grind)
          | exact resolve b7e192059 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e192059
        have b7e194557 : x ≠ y := by
          first
          | (have i₁ := b7e20
             have i₂ := b7e192066
             grind)
          | exact superpose b7e192066 b7e20
          | exact resolve b7e20 b7e192066
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e194569 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ (τ X0) = (τ x) := by
          intro X0
          first
          | (have i₁ := b7e64752 X0 y
             have i₂ := b7e192066
             grind)
          | exact superpose b7e192066 b7e64752
          | (have j0 := b7e64752 X0 y
             grind)
          | exact resolve b7e64752 b7e192066
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e64752
        have b7e194571 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b7e11 X0 y y
             have i₂ := b7e192066
             grind)
          | exact superpose b7e192066 b7e11
          | exact resolve b7e11 b7e192066
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e194576 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op X0 y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b7e32 X0 y X1 y
             have i₂ := b7e192066
             grind)
          | exact superpose b7e192066 b7e32
          | exact resolve b7e32 b7e192066
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e32
        have b7e194632 : (M.op y x) = (M.op y (M.op y x)) := by
          first
          | (have i₁ := b7e233 y y
             have i₂ := b7e192066
             grind)
          | exact superpose b7e192066 b7e233
          | exact resolve b7e233 b7e192066
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e233
        have b7e194668 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) X0) := by
          intro X0
          first
          | (have i₁ := b7e384 y y x
             have i₂ := b7e192066
             grind)
          | exact superpose b7e192066 b7e384
          | exact resolve b7e384 b7e192066
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e384
        have b7e194696 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op y (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b7e593 X0 y y
             have i₂ := b7e192066
             grind)
          | exact superpose b7e192066 b7e593
          | exact resolve b7e593 b7e192066
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e593
        have b7e194759 : (M.op y (M.op y y)) = (M.op y (M.op y x)) := by
          first
          | (have i₁ := b7e194696 x
             have i₂ := b7e11 y y x
             grind)
          | exact superpose b7e11 b7e194696
          | exact resolve b7e194696 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e194696
        have b7e194823 : (M.op y x) = (M.op y (M.op y y)) := by
          first
          | (have i₁ := b7e194759
             have i₂ := b7e194632
             grind)
          | exact superpose b7e194632 b7e194759
          | exact resolve b7e194759 b7e194632
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e194632 b7e194759
        have b7e194869 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b7e194823
             have i₂ := b7e194571 y
             grind)
          | exact superpose b7e194571 b7e194823
          | exact resolve b7e194823 b7e194571
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e194571 b7e194823
        have b7e270622 : y = (M.op (k y y) y) ∨ y = (M.op y y) ∨ (τ x) = (τ (k y y)) := by
          first
          | (have i₁ := b7e18276 y
             have i₂ := b7e194569 (k y y)
             grind)
          | exact superpose b7e194569 b7e18276
          | (have j0 := b7e18276 y
             have j1 := b7e194569 (k y y)
             grind)
          | exact resolve b7e18276 b7e194569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e18276 b7e194569
        have b7e270631 : y = (M.op (k y y) y) ∨ (τ x) = (τ (k y y)) := by
          first
          | (have r₁ := b7e270622
             have r₂ := b7e20
             grind)
          | exact resolve b7e270622 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e270622
        have b7e387455 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ (τ x) = (τ (k y y)) := by
          intro X0
          first
          | (have i₁ := b7e194576 (k y y) X0
             have i₂ := b7e270631
             grind)
          | exact superpose b7e270631 b7e194576
          | exact resolve b7e194576 b7e270631
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e194576 b7e270631
        have b7e426123 : ∀ X0 : G, (k y y) = (σ (τ x)) ∨ (M.op x X0) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b7e13 (k y y)
             have i₂ := b7e387455 X0
             grind)
          | exact superpose b7e387455 b7e13
          | (have j1 := b7e387455 X0
             grind)
          | exact resolve b7e13 b7e387455
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e387455
        have b7e426132 : ∀ X0 : G, x = (k y y) ∨ (M.op x X0) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b7e426123 X0
             have i₂ := b7e13 x
             grind)
          | exact superpose b7e13 b7e426123
          | (have j0 := b7e426123 X0
             grind)
          | exact resolve b7e426123 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e426123
        have b7e426264 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) X0) ∨ x = (k y y) := by
          intro X0
          first
          | (have i₁ := b7e194668 X0
             have i₂ := b7e426132 X0
             grind)
          | exact superpose b7e426132 b7e194668
          | exact resolve b7e194668 b7e426132
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e194668 b7e426132
        have b7e428601 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
          intro X0
          first
          | (have j0 := b7e7873 (τ X0) X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e7873
        have b7e428602 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b7e428601 X0
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e428601
          | (have j0 := b7e428601 X0
             grind)
          | exact resolve b7e428601 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e428601
        have b7e428615 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
          intro X0
          first
          | (have i₁ := b7e428602 (σ X0)
             have i₂ := b7e16 X0 X0
             grind)
          | exact superpose b7e16 b7e428602
          | (have j0 := b7e428602 (σ X0)
             grind)
          | exact resolve b7e428602 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e428602
        have b7e428632 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b7e428615 X0
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e428615
          | (have j0 := b7e428615 X0
             grind)
          | exact resolve b7e428615 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e428615
        have b7e428689 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b7e428632 X0
             have i₂ := b7e14791 X0 X0
             grind)
          | exact superpose b7e14791 b7e428632
          | (have j0 := b7e428632 X0
             have j1 := b7e14791 X0 X0
             grind)
          | (have r₁ := b7e428632 x
             have r₂ := b7e14791 x x
             grind)
          | exact resolve b7e428632 b7e14791
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e14791 b7e428632
        have b7e428694 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b7e428689 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e428689
        have b7e428901 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b7e428694 y
             have i₂ := b7e192066
             grind)
          | exact superpose b7e192066 b7e428694
          | exact resolve b7e428694 b7e192066
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e428694
        have b7e432151 : x = (k x y) ∨ x = (k y y) := by
          first
          | (have i₁ := b7e426264 y
             have i₂ := b7e192066
             grind)
          | exact superpose b7e192066 b7e426264
          | exact resolve b7e426264 b7e192066
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e192066 b7e426264
        have b7e432470 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x x) ∨ x = (k y y) := by
          first
          | (have i₁ := b7e8004 y x
             have i₂ := b7e432151
             grind)
          | exact superpose b7e432151 b7e8004
          | (have j0 := b7e8004 y x
             grind)
          | exact resolve b7e8004 b7e432151
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e8004 b7e432151
        have b7e432476 : (σ x) = (σ (M.op y x)) ∨ x = (k y y) := by
          first
          | (have r₁ := b7e432470
             have r₂ := b7e18
             grind)
          | exact resolve b7e432470 b7e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e432470
        have b7e435179 : (σ y) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b7e23534
             have i₂ := b7e194869
             grind)
          | exact superpose b7e194869 b7e23534
          | exact resolve b7e23534 b7e194869
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e23534
        have b7e454568 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) := by
          first
          | (have i₁ := b7e435179
             have i₂ := b7e432476
             grind)
          | exact superpose b7e432476 b7e435179
          | exact resolve b7e435179 b7e432476
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e432476 b7e435179
        have b7e454569 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) := by
          first
          | (have r₁ := b7e454568
             have r₂ := b7e428901
             grind)
          | exact resolve b7e454568 b7e428901
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e428901 b7e454568
        have b7e454578 : (σ x) = (σ (k y y)) ∨ y = (M.op y y) ∨ x = (k y y) := by
          first
          | (have i₁ := b7e185299 y
             have i₂ := b7e454569
             grind)
          | exact superpose b7e454569 b7e185299
          | (have j0 := b7e185299 y
             grind)
          | exact resolve b7e185299 b7e454569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e454569
        have b7e454616 : (σ x) = (σ (k y y)) ∨ x = (k y y) := by
          first
          | (have r₁ := b7e454578
             have r₂ := b7e20
             grind)
          | exact resolve b7e454578 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e454578
        have b7e454788 : (k y y) = (τ (σ x)) ∨ x = (k y y) := by
          first
          | (have i₁ := b7e12 (k y y)
             have i₂ := b7e454616
             grind)
          | exact superpose b7e454616 b7e12
          | exact resolve b7e12 b7e454616
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e454616
        have b7e454799 : x = (k y y) ∨ x = (k y y) := by
          first
          | (have i₁ := b7e454788
             have i₂ := b7e12 x
             grind)
          | exact superpose b7e12 b7e454788
          | exact resolve b7e454788 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e454788
        have b7e454800 : x = (k y y) := by grind
        clear b7e454799
        have b7e507432 : x = (τ (σ y)) ∨ (k x (τ (σ y))) = (M.op (τ (σ y)) x) := by
          first
          | (have j0 := b7e183237 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e183237
        have b7e507433 : x = y ∨ (k x (τ (σ y))) = (M.op (τ (σ y)) x) := by
          first
          | (have i₁ := b7e507432
             have i₂ := b7e12 y
             grind)
          | exact superpose b7e12 b7e507432
          | exact resolve b7e507432 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e507432
        have b7e507434 : (k x (τ (σ y))) = (M.op (τ (σ y)) x) := by
          first
          | (have r₁ := b7e507433
             have r₂ := b7e194557
             grind)
          | exact resolve b7e507433 b7e194557
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e507433
        have b7e507435 : (k x y) = (M.op y x) := by
          first
          | (have i₁ := b7e507434
             have i₂ := b7e12 y
             grind)
          | exact superpose b7e12 b7e507434
          | exact resolve b7e507434 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e507434
        have b7e524493 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (σ y) X0)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b7e76262 y y x
             have i₂ := b7e454800
             grind)
          | exact superpose b7e454800 b7e76262
          | exact resolve b7e76262 b7e454800
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e76262
        have b7e524504 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (σ y) X0)) := by
          intro X0
          first
          | (have j0 := b7e524493 X0
             grind)
          | (have r₁ := b7e524493 X0
             have r₂ := b7e194557
             grind)
          | exact resolve b7e524493 b7e194557
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e194557 b7e524493
        have b7e524515 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (k y y))) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b7e524504 (σ y)
             have i₂ := b7e185299 y
             grind)
          | exact superpose b7e185299 b7e524504
          | (have j1 := b7e185299 y
             grind)
          | exact resolve b7e524504 b7e185299
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e185299 b7e524504
        have b7e524921 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (k y y))) := by
          first
          | (have r₁ := b7e524515
             have r₂ := b7e20
             grind)
          | exact resolve b7e524515 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e524515
        have b7e524941 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b7e524921
             have i₂ := b7e454800
             grind)
          | exact superpose b7e454800 b7e524921
          | exact resolve b7e524921 b7e454800
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e454800 b7e524921
        have b7e524951 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b7e524941
             have i₂ := b7e185
             grind)
          | exact superpose b7e185 b7e524941
          | exact resolve b7e524941 b7e185
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e185 b7e524941
        have b7e524958 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b7e524951
             have i₂ := b7e507435
             grind)
          | exact superpose b7e507435 b7e524951
          | exact resolve b7e524951 b7e507435
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e507435 b7e524951
        have b7e524968 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e524958
             grind)
          | exact superpose b7e524958 b7e17
          | exact resolve b7e17 b7e524958
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e524958
        have b7e525104 : (σ (M.op y x)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b7e524968
             have i₂ := b7e194869
             grind)
          | exact superpose b7e194869 b7e524968
          | exact resolve b7e524968 b7e194869
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e194869 b7e524968
        have b7e525105 : False := by grind
        exact b7e525105

/-- `Equation4456`: `x ◇ (y ◇ x) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation4456 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4456 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4456.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
        intro X0 X1 X2
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op y x) := by grind
      have b0e18 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e32 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e10 (σ x) (σ y) X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X2 X1 X3
           have i₂ := b0e10 X2 X1 X0
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X3 (M.op X1 X2) X2
           have i₂ := b0e10 X2 X1 X0
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X2 X0 (M.op x X1)
           have i₂ := b0e10 X0 X1 x
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 x y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : (M.op y (M.op x x)) = (M.op (M.op x x) (M.op y x)) := by
        first
        | (have i₁ := b0e37 (M.op x x)
           have i₂ := b0e37 x
           grind)
        | exact superpose b0e37 b0e37
        | exact resolve b0e37 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 x X1
           have i₂ := b0e37 X0
           grind)
        | exact superpose b0e37 b0e10
        | exact resolve b0e10 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) X1)) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X1 (M.op x X0) X0
           have i₂ := b0e37 X0
           grind)
        | exact superpose b0e37 b0e10
        | exact resolve b0e10 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e46 : (M.op y (M.op x x)) = (M.op y (M.op y x)) := by
        first
        | (have i₁ := b0e40
           have i₂ := b0e42 (M.op y x) x
           grind)
        | exact superpose b0e42 b0e40
        | exact resolve b0e40 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e47 : (M.op y (M.op x x)) = (M.op y y) := by
        first
        | (have i₁ := b0e46
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e46
        | exact resolve b0e46 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e73 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) X0)) = (M.op (M.op y y) X0) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 (M.op x x) y
           have i₂ := b0e47
           grind)
        | exact superpose b0e47 b0e10
        | exact resolve b0e10 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e77 : ∀ X0 : G, (M.op (M.op y x) X0) = (M.op (M.op y y) X0) := by
        intro X0
        first
        | (have i₁ := b0e73 X0
           have i₂ := b0e43 x X0
           grind)
        | exact superpose b0e43 b0e73
        | exact resolve b0e73 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e73
      have b0e79 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y y) X0) := by
        intro X0
        first
        | (have i₁ := b0e77 X0
           have i₂ := b0e42 X0 y
           grind)
        | exact superpose b0e42 b0e77
        | exact resolve b0e77 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e77
      have b0e101 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e33 X0 (σ x) X1 (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e33
        | exact resolve b0e33 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e137 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 y y
           have i₂ := b0e79 X0
           grind)
        | exact superpose b0e79 b0e10
        | exact resolve b0e10 b0e79
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79
      have b0e218 : y = (M.op x y) := by
        first
        | (have i₁ := b0e137 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e137
        | exact resolve b0e137 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e137
      have b0e314 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X0 (M.op X2 X1) X1
           have i₂ := b0e35 X1 X2 X0
           grind)
        | exact superpose b0e35 b0e10
        | exact resolve b0e10 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e561 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ y)) (σ x)) X0) = (M.op X0 (M.op (σ y) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e34 X1 (σ y) (σ x) X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e34
        | exact resolve b0e34 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e674 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (M.op X0 X1) (σ y))) (σ x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e32 (M.op (M.op x X0) X1)
           have i₂ := b0e34 x X0 X1 (σ y)
           grind)
        | exact superpose b0e34 b0e32
        | exact resolve b0e32 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e34
      have b0e677 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op X0 X1) (σ y)) (σ x))) := by
        intro X0 X1
        first
        | (have i₁ := b0e674 X0 X1
           have i₂ := b0e10 (σ x) (M.op (M.op X0 X1) (σ y)) (σ y)
           grind)
        | exact superpose b0e10 b0e674
        | exact resolve b0e674 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e674
      have b0e718 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e561 X0 x
           have i₂ := b0e101 (M.op x (σ y)) X0
           grind)
        | exact superpose b0e101 b0e561
        | exact resolve b0e561 b0e101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e101 b0e561
      have b0e724 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
        first
        | (have i₁ := b0e677 x x
           have i₂ := b0e314 (σ x) (σ y) (M.op x x)
           grind)
        | exact superpose b0e314 b0e677
        | exact resolve b0e677 b0e314
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e314 b0e677
      have b0e740 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e724
           have i₂ := b0e718 (σ x)
           grind)
        | exact superpose b0e718 b0e724
        | exact resolve b0e724 b0e718
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e718 b0e724
      have b0e744 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e740
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e740
        | exact resolve b0e740 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e740
      have b0e745 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e744
           grind)
        | exact superpose b0e744 b0e16
        | exact resolve b0e16 b0e744
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e744
      have b0e759 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e745
           have i₂ := b0e218
           grind)
        | exact superpose b0e218 b0e745
        | exact resolve b0e745 b0e218
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e218 b0e745
      have b0e760 : False := by grind
      exact b0e760
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
        intro X0 X1 X2
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b1e17 : y = (M.op y x) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e19 : y ≠ y ∨ x = (k x y) := by
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
      have b1e20 : x = (k x y) := by grind
      clear b1e19
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
      have b1e22 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b1e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X0 (M.op X2 X1) X3
           have i₂ := b1e10 X0 X1 X2
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X2 X1 X3
           have i₂ := b1e10 X2 X1 X0
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e30 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b1e10 X0 x y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e32 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 X2 X0 (M.op x X1)
           have i₂ := b1e10 X0 X1 x
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e35 : (M.op y (M.op x x)) = (M.op (M.op x x) (M.op y x)) := by
        first
        | (have i₁ := b1e30 (M.op x x)
           have i₂ := b1e30 x
           grind)
        | exact superpose b1e30 b1e30
        | exact resolve b1e30 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e37 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 x X1
           have i₂ := b1e30 X0
           grind)
        | exact superpose b1e30 b1e10
        | exact resolve b1e10 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e38 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) X1)) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X1 (M.op x X0) X0
           have i₂ := b1e30 X0
           grind)
        | exact superpose b1e30 b1e10
        | exact resolve b1e10 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e41 : (M.op y (M.op x x)) = (M.op y (M.op y x)) := by
        first
        | (have i₁ := b1e35
           have i₂ := b1e37 (M.op y x) x
           grind)
        | exact superpose b1e37 b1e35
        | exact resolve b1e35 b1e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35
      have b1e42 : (M.op y (M.op x x)) = (M.op y y) := by
        first
        | (have i₁ := b1e41
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e41
        | exact resolve b1e41 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e41
      have b1e45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
      have b1e46 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e21 X0 X1
           have i₂ := b1e14 (τ X0) X1
           grind)
        | exact superpose b1e14 b1e21
        | (have j1 := b1e14 (τ X0) X1
           grind)
        | exact resolve b1e21 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e56 : ∀ X0 X1 : G, (M.op y X0) ≠ (M.op X1 x) ∨ (k X0 (M.op X1 x)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e13 X0 (M.op X1 x)
           have i₂ := b1e37 X0 X1
           grind)
        | exact superpose b1e37 b1e13
        | (have j0 := b1e13 X0 (M.op X1 x)
           grind)
        | (have r₁ := b1e13 x (M.op y x)
           have r₂ := b1e37 x y
           grind)
        | exact resolve b1e13 b1e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e65 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k X0 (τ X1))
           have i₂ := b1e22 X1 X0
           grind)
        | exact superpose b1e22 b1e11
        | exact resolve b1e11 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e68 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) X0)) = (M.op (M.op y y) X0) := by
        intro X0
        first
        | (have i₁ := b1e10 X0 (M.op x x) y
           have i₂ := b1e42
           grind)
        | exact superpose b1e42 b1e10
        | exact resolve b1e10 b1e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e42
      have b1e72 : ∀ X0 : G, (M.op (M.op y x) X0) = (M.op (M.op y y) X0) := by
        intro X0
        first
        | (have i₁ := b1e68 X0
           have i₂ := b1e38 x X0
           grind)
        | exact superpose b1e38 b1e68
        | exact resolve b1e68 b1e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38 b1e68
      have b1e74 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y y) X0) := by
        intro X0
        first
        | (have i₁ := b1e72 X0
           have i₂ := b1e37 X0 y
           grind)
        | exact superpose b1e37 b1e72
        | exact resolve b1e72 b1e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e37 b1e72
      have b1e115 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X1) ∨ (k X2 (M.op X3 X1)) = X2 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e13 X2 (M.op X3 X1)
           have i₂ := b1e29 X3 X1 X2 X0
           grind)
        | (have i₁ := b1e13 X2 (M.op X3 X1)
           have i₂ := b1e29 X0 X1 X2 X3
           grind)
        | exact superpose b1e29 b1e13
        | (have j0 := b1e13 X2 (M.op X3 X1)
           grind)
        | (have r₁ := b1e13 X2 (M.op (M.op X3 X2) X2)
           have r₂ := b1e29 (M.op X3 X2) X2 X2 X3
           grind)
        | (have r₁ := b1e13 X2 (M.op (M.op X0 X2) X2)
           have r₂ := b1e29 X0 X2 X2 (M.op X0 X2)
           grind)
        | exact resolve b1e13 b1e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e29
      have b1e130 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b1e10 X0 y y
           have i₂ := b1e74 X0
           grind)
        | exact superpose b1e74 b1e10
        | exact resolve b1e10 b1e74
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e74
      have b1e299 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e32 X1 x X0
           have i₂ := b1e28 X0 X1 x X1
           grind)
        | exact superpose b1e28 b1e32
        | exact resolve b1e32 b1e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28 b1e32
      have b1e399 : y = (M.op x y) := by
        first
        | (have i₁ := b1e130 x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e130
        | exact resolve b1e130 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e130
      have b1e722 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e26 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e26
        | exact resolve b1e26 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e26
      have b1e961 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e45 X1 X0
           have i₂ := b1e45 X0 X1
           grind)
        | exact superpose b1e45 b1e45
        | (have j0 := b1e45 X1 X0
           have j1 := b1e45 X1 X0
           grind)
        | exact resolve b1e45 b1e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e962 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e45 x y
           grind)
        | exact superpose b1e45 b1e16
        | (have j1 := b1e45 x y
           grind)
        | exact resolve b1e16 b1e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e964 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X1) X2)) = (M.op (σ (k X0 X1)) X2) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 X2 (σ X1) (σ X0)
           have i₂ := b1e45 X0 X1
           grind)
        | exact superpose b1e45 b1e10
        | (have j1 := b1e45 X0 X1
           grind)
        | exact resolve b1e10 b1e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e965 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 (σ X1) (σ X0)
           have i₂ := b1e45 X0 X1
           grind)
        | exact superpose b1e45 b1e13
        | (have j0 := b1e13 (σ X1) (σ X0)
           have j1 := b1e45 X0 X1
           grind)
        | (have r₁ := b1e13 (σ X0) (σ X1)
           have r₂ := b1e45 X0 X1
           grind)
        | exact resolve b1e13 b1e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e983 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 (σ X1) (σ X0)
           have i₂ := b1e45 X1 X0
           grind)
        | exact superpose b1e45 b1e13
        | (have j0 := b1e13 (σ X1) (σ X0)
           have j1 := b1e45 X1 X0
           grind)
        | (have r₁ := b1e13 (σ X0) (σ X1)
           have r₂ := b1e45 X0 X1
           grind)
        | exact resolve b1e13 b1e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e998 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b1e45 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e45
      have b1e999 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e983 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e983
      have b1e1001 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e999 X0 X1
           have i₂ := b1e15 X1 X0
           grind)
        | exact superpose b1e15 b1e999
        | (have j0 := b1e999 X0 X1
           grind)
        | exact resolve b1e999 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e999
      have b1e1004 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e965 X0 X1
           have i₂ := b1e15 X1 X0
           grind)
        | exact superpose b1e15 b1e965
        | (have j0 := b1e965 X0 X1
           grind)
        | exact resolve b1e965 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e965
      have b1e1005 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have r₁ := b1e962
           have r₂ := b1e18
           grind)
        | exact resolve b1e962 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e962
      have b1e1010 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b1e1005
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e1005
        | exact resolve b1e1005 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1005
      have b1e1011 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e1010
           have i₂ := b1e399
           grind)
        | exact superpose b1e399 b1e1010
        | exact resolve b1e1010 b1e399
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e399 b1e1010
      have b1e13128 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b1e998 (τ X0)
           have i₂ := b1e22 X0 (τ X0)
           grind)
        | exact superpose b1e22 b1e998
        | (have j0 := b1e998 (τ X0)
           grind)
        | exact resolve b1e998 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e998
      have b1e13129 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b1e13128 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e13128
        | (have j0 := b1e13128 X0
           grind)
        | exact resolve b1e13128 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13128
      have b1e13132 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b1e13129 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e13129
        | (have j0 := b1e13129 X0
           grind)
        | exact resolve b1e13129 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13129
      have b1e13138 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
        intro X0
        first
        | (have i₁ := b1e13132 (τ X0)
           have i₂ := b1e722 X0 X0
           grind)
        | exact superpose b1e722 b1e13132
        | (have j0 := b1e13132 (τ X0)
           grind)
        | exact resolve b1e13132 b1e722
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13132
      have b1e13662 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e46 (σ X0) X1
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e46
        | exact resolve b1e46 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e46
      have b1e13713 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e13662 X0 X1
           have i₂ := b1e15 X0 X1
           grind)
        | exact superpose b1e15 b1e13662
        | (have j0 := b1e13662 X0 X1
           grind)
        | exact resolve b1e13662 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13662
      have b1e14228 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X0) X0)) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e115 X0 X0 X0 (M.op X1 X0)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e115
      have b1e14324 : ∀ X0 : G, (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e14228 X0 x
           have i₂ := b1e10 X0 X0 x
           grind)
        | exact superpose b1e10 b1e14228
        | exact resolve b1e14228 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e15405 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))) := by
        intro X0
        first
        | (have i₁ := b1e65 X0 (M.op (σ X0) (M.op (σ X0) (σ X0)))
           have i₂ := b1e14324 (σ X0)
           grind)
        | exact superpose b1e14324 b1e65
        | exact resolve b1e65 b1e14324
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e14324
      have b1e15408 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e15405 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e15405
        | exact resolve b1e15405 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e15405
      have b1e28491 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e1001 X0 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e1001
        | exact resolve b1e1001 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1001
      have b1e28597 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e28491 X0 X1
           have i₂ := b1e21 X0 X1
           grind)
        | exact superpose b1e21 b1e28491
        | (have j0 := b1e28491 X0 X1
           grind)
        | exact resolve b1e28491 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28491
      have b1e28600 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e28597 X0 X1
           have i₂ := b1e21 X0 X1
           grind)
        | exact superpose b1e21 b1e28597
        | (have j0 := b1e28597 X0 X1
           grind)
        | exact resolve b1e28597 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28597
      have b1e28601 : ∀ X0 : G, y ≠ (M.op X0 x) ∨ x = (k x (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b1e56 x X0
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e56
        | (have j0 := b1e56 x X0
           grind)
        | exact resolve b1e56 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e56
      have b1e83716 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e28600 X0 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e28600
        | exact resolve b1e28600 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28600
      have b1e88051 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e83716 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e83716
      have b1e89734 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        intro X0
        first
        | (have i₁ := b1e964 x y X0
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e964
        | (have j0 := b1e964 x y x
           grind)
        | exact resolve b1e964 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e964
      have b1e90450 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b1e89734 X0
           grind)
        | (have r₁ := b1e89734 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e89734 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e89734
      have b1e91748 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (σ x) X0)) := by
        intro X0
        first
        | (have i₁ := b1e299 X0 (σ y)
           have i₂ := b1e90450 X0
           grind)
        | exact superpose b1e90450 b1e299
        | exact resolve b1e299 b1e90450
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e299 b1e90450
      have b1e97508 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X1 (σ x)) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 (σ x) X1
           have i₂ := b1e91748 X0
           grind)
        | exact superpose b1e91748 b1e10
        | exact resolve b1e10 b1e91748
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e97807 : x = (k x (τ (M.op (σ x) (σ x)))) := by
        first
        | (have i₁ := b1e15408 x
           have i₂ := b1e91748 (σ x)
           grind)
        | exact superpose b1e91748 b1e15408
        | exact resolve b1e15408 b1e91748
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e15408 b1e91748
      have b1e101588 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e1004 (τ X0) (τ X1)
           have i₂ := b1e722 X1 X0
           grind)
        | exact superpose b1e722 b1e1004
        | (have j0 := b1e1004 (τ X0) (τ X1)
           grind)
        | exact resolve b1e1004 b1e722
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1004
      have b1e101625 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e101588 X0 X1
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e101588
        | (have j0 := b1e101588 X0 X1
           grind)
        | exact resolve b1e101588 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e101588
      have b1e101636 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e101625 X0 X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e101625
        | (have j0 := b1e101625 X0 X1
           grind)
        | exact resolve b1e101625 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e101625
      have b1e101644 : ∀ X0 X1 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e101636 X0 X1
           have i₂ := b1e22 X0 (τ X1)
           grind)
        | exact superpose b1e22 b1e101636
        | (have j0 := b1e101636 X0 X1
           grind)
        | exact resolve b1e101636 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e101636
      have b1e101650 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e101644 X0 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e101644
        | (have j0 := b1e101644 X0 X1
           grind)
        | exact resolve b1e101644 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e101644
      have b1e101651 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e101650 X0 X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e101650
        | (have j0 := b1e101650 X0 X1
           grind)
        | exact resolve b1e101650 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e101650
      have b1e101652 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e101651 X0 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e101651
        | (have j0 := b1e101651 X0 X1
           grind)
        | exact resolve b1e101651 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e101651
      have b1e101653 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b1e101652 X0 X1
           have j1 := b1e88051 X1 X0
           grind)
        | (have r₁ := b1e101652 X1 X0
           have r₂ := b1e88051 X0 X1
           grind)
        | (have r₁ := b1e101652 X0 X1
           have r₂ := b1e88051 X0 X1
           grind)
        | exact resolve b1e101652 b1e88051
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e88051 b1e101652
      have b1e101674 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (k (τ X1) (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e101653 (τ X0) (τ X1)
           have i₂ := b1e722 X1 X0
           grind)
        | exact superpose b1e722 b1e101653
        | (have j0 := b1e101653 (τ X0) (τ X1)
           grind)
        | exact resolve b1e101653 b1e722
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e101653
      have b1e101703 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e101674 X0 X1
           have i₂ := b1e722 X0 X1
           grind)
        | exact superpose b1e722 b1e101674
        | (have j0 := b1e101674 X0 X1
           grind)
        | exact resolve b1e101674 b1e722
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e722 b1e101674
      have b1e200820 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e961 (τ X0) X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e961
        | exact resolve b1e961 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e961
      have b1e201106 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e200820 X0 X1
           have i₂ := b1e22 X0 X1
           grind)
        | exact superpose b1e22 b1e200820
        | (have j0 := b1e200820 X0 X1
           grind)
        | exact resolve b1e200820 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22 b1e200820
      have b1e201117 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e201106 X0 X1
           have i₂ := b1e21 X0 X1
           grind)
        | exact superpose b1e21 b1e201106
        | (have j0 := b1e201106 X0 X1
           grind)
        | exact resolve b1e201106 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21 b1e201106
      have b1e201120 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
        intro X0 X1
        first
        | (have j0 := b1e201117 X0 X1
           have j1 := b1e13 X0 (σ X1)
           grind)
        | (have r₁ := b1e201117 X0 X1
           have r₂ := b1e13 X0 (σ X1)
           grind)
        | exact resolve b1e201117 b1e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e201117
      have b1e201135 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e201120 X0 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e201120
        | exact resolve b1e201120 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e201165 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e65 X0 (σ X1)
           have i₂ := b1e201120 (σ X0) X1
           grind)
        | exact superpose b1e201120 b1e65
        | (have j1 := b1e201120 (σ X0) X1
           grind)
        | exact resolve b1e65 b1e201120
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e65 b1e201120
      have b1e201232 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e201165 X0 X1
           have i₂ := b1e11 X1
           grind)
        | exact superpose b1e11 b1e201165
        | (have j0 := b1e201165 X0 X1
           grind)
        | exact resolve b1e201165 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e201165
      have b1e201255 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e201232 X0 X1
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e201232
        | (have j0 := b1e201232 X0 X1
           grind)
        | exact resolve b1e201232 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e201232
      have b1e201263 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e201255 X0 X1
           have i₂ := b1e15 X1 X0
           grind)
        | exact superpose b1e15 b1e201255
        | (have j0 := b1e201255 X0 X1
           grind)
        | exact resolve b1e201255 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e201255
      have b1e201471 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X1) = (τ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e101703 X0 X1
           have i₂ := b1e201135 X1 X0
           grind)
        | exact superpose b1e201135 b1e101703
        | (have j0 := b1e101703 X0 X1
           have j1 := b1e201135 X1 X0
           grind)
        | exact resolve b1e101703 b1e201135
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e101703 b1e201135
      have b1e201504 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b1e201471 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e201471
      have b1e203317 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (M.op X0 X0) := by
        intro X0
        first
        | (have i₁ := b1e13138 X0
           have i₂ := b1e201504 X0 X0
           grind)
        | exact superpose b1e201504 b1e13138
        | (have j0 := b1e13138 X0
           have j1 := b1e201504 X0 X0
           grind)
        | (have r₁ := b1e13138 X0
           have r₂ := b1e201504 X0 X0
           grind)
        | exact resolve b1e13138 b1e201504
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13138 b1e201504
      have b1e203336 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (M.op X0 X0) := by
        intro X0
        first
        | (have j0 := b1e203317 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e203317
      have b1e216266 : x = (k x (τ (σ (k x x)))) ∨ x = (k x x) := by
        first
        | (have i₁ := b1e97807
           have i₂ := b1e201263 x x
           grind)
        | exact superpose b1e201263 b1e97807
        | (have j1 := b1e201263 x (τ (σ (k x x)))
           grind)
        | exact resolve b1e97807 b1e201263
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e97807 b1e201263
      have b1e216492 : x = (k x (k x x)) ∨ x = (k x x) := by
        first
        | (have i₁ := b1e216266
           have i₂ := b1e11 (k x x)
           grind)
        | exact superpose b1e11 b1e216266
        | exact resolve b1e216266 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e216266
      have b1e218985 : x = (k x (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e216492
           have i₂ := b1e14 x x
           grind)
        | exact superpose b1e14 b1e216492
        | (have j1 := b1e14 x x
           grind)
        | exact resolve b1e216492 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e216492
      have b1e218998 : x = (k x (M.op x x)) ∨ x = (M.op x x) := by grind
      clear b1e218985
      have b1e221850 : (σ x) = (σ (M.op x (M.op x x))) ∨ (M.op x x) = (M.op (M.op x x) x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e13713 x (M.op x x)
           have i₂ := b1e218998
           grind)
        | exact superpose b1e218998 b1e13713
        | (have j0 := b1e13713 x (M.op x x)
           grind)
        | exact resolve b1e13713 b1e218998
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e218998
      have b1e221857 : (σ x) = (σ (M.op y x)) ∨ (M.op x x) = (M.op (M.op x x) x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e221850
           have i₂ := b1e30 x
           grind)
        | exact superpose b1e30 b1e221850
        | exact resolve b1e221850 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e221850
      have b1e221860 : (σ x) = (σ y) ∨ (M.op x x) = (M.op (M.op x x) x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e221857
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e221857
        | exact resolve b1e221857 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e221857
      have b1e221863 : (M.op x x) = (M.op (M.op x x) x) ∨ x = (M.op x x) := by
        first
        | (have r₁ := b1e221860
           have r₂ := b1e1011
           grind)
        | exact resolve b1e221860 b1e1011
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e221860
      have b1e221866 : (M.op x x) = (M.op x (M.op x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e221863
           have i₂ := b1e10 x x x
           grind)
        | exact superpose b1e10 b1e221863
        | exact resolve b1e221863 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e221863
      have b1e221869 : (M.op y x) = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e221866
           have i₂ := b1e30 x
           grind)
        | exact superpose b1e30 b1e221866
        | exact resolve b1e221866 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e221866
      have b1e221872 : x = (M.op x x) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b1e221869
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e221869
        | exact resolve b1e221869 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e221869
      have b1e225031 : x = (k x (M.op x x)) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b1e14228 x x
           have i₂ := b1e221872
           grind)
        | exact superpose b1e221872 b1e14228
        | exact resolve b1e14228 b1e221872
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e14228 b1e221872
      have b1e225041 : x = (k x (M.op x x)) := by
        first
        | (have j1 := b1e28601 x
           grind)
        | (have r₁ := b1e225031
           have r₂ := b1e28601 x
           grind)
        | exact resolve b1e225031 b1e28601
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28601 b1e225031
      have b1e227341 : (σ x) = (σ (M.op x (M.op x x))) ∨ (M.op x x) = (M.op (M.op x x) x) := by
        first
        | (have i₁ := b1e13713 x (M.op x x)
           have i₂ := b1e225041
           grind)
        | exact superpose b1e225041 b1e13713
        | (have j0 := b1e13713 x (M.op x x)
           grind)
        | exact resolve b1e13713 b1e225041
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e225041
      have b1e227349 : (σ x) = (σ (M.op y x)) ∨ (M.op x x) = (M.op (M.op x x) x) := by
        first
        | (have i₁ := b1e227341
           have i₂ := b1e30 x
           grind)
        | exact superpose b1e30 b1e227341
        | exact resolve b1e227341 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e227341
      have b1e227356 : (σ x) = (σ y) ∨ (M.op x x) = (M.op (M.op x x) x) := by
        first
        | (have i₁ := b1e227349
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e227349
        | exact resolve b1e227349 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e227349
      have b1e227360 : (M.op x x) = (M.op (M.op x x) x) := by
        first
        | (have r₁ := b1e227356
           have r₂ := b1e1011
           grind)
        | exact resolve b1e227356 b1e1011
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e227356
      have b1e227363 : (M.op x x) = (M.op x (M.op x x)) := by
        first
        | (have i₁ := b1e227360
           have i₂ := b1e10 x x x
           grind)
        | exact superpose b1e10 b1e227360
        | exact resolve b1e227360 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e227360
      have b1e227366 : (M.op y x) = (M.op x x) := by
        first
        | (have i₁ := b1e227363
           have i₂ := b1e30 x
           grind)
        | exact superpose b1e30 b1e227363
        | exact resolve b1e227363 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30 b1e227363
      have b1e227369 : y = (M.op x x) := by
        first
        | (have i₁ := b1e227366
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e227366
        | exact resolve b1e227366 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e227366
      have b1e330907 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e203336 (σ X0)
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e203336
        | (have j0 := b1e203336 (σ X0)
           grind)
        | exact resolve b1e203336 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e203336
      have b1e331036 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b1e330907 X0
           have i₂ := b1e15 X0 X0
           grind)
        | exact superpose b1e15 b1e330907
        | (have j0 := b1e330907 X0
           grind)
        | exact resolve b1e330907 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e330907
      have b1e338770 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (k x x)) X0) ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b1e97508 X0 (σ x)
           have i₂ := b1e331036 x
           grind)
        | exact superpose b1e331036 b1e97508
        | (have j1 := b1e331036 x
           grind)
        | exact resolve b1e97508 b1e331036
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e97508
      have b1e338874 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (k x x)) X0) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b1e338770 X0
           have i₂ := b1e227369
           grind)
        | exact superpose b1e227369 b1e338770
        | (have j0 := b1e338770 X0
           grind)
        | exact resolve b1e338770 b1e227369
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e338770
      have b1e340047 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (σ x) X0) ∨ x = y ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b1e338874 X0
           have i₂ := b1e13713 x x
           grind)
        | exact superpose b1e13713 b1e338874
        | (have j1 := b1e13713 x x
           grind)
        | exact resolve b1e338874 b1e13713
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e338874
      have b1e340323 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ x = y ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b1e340047 X0
           have i₂ := b1e227369
           grind)
        | exact superpose b1e227369 b1e340047
        | exact resolve b1e340047 b1e227369
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e340047
      have b1e340333 : ∀ X0 : G, x = y ∨ (M.op (σ y) X0) = (M.op (σ x) X0) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b1e340323 X0
           have i₂ := b1e227369
           grind)
        | exact superpose b1e227369 b1e340323
        | (have j0 := b1e340323 X0
           grind)
        | exact resolve b1e340323 b1e227369
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e340323
      have b1e340334 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ x = y := by
        intro X0
        first
        | (have j0 := b1e340333 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e340333
      have b1e340511 : (M.op (σ y) (σ x)) = (σ (k x x)) ∨ x = (M.op x x) ∨ x = y := by
        first
        | (have i₁ := b1e331036 x
           have i₂ := b1e340334 (σ x)
           grind)
        | exact superpose b1e340334 b1e331036
        | (have j0 := b1e331036 x
           grind)
        | exact resolve b1e331036 b1e340334
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e331036 b1e340334
      have b1e340822 : x = y ∨ (M.op (σ y) (σ x)) = (σ (k x x)) ∨ x = y := by
        first
        | (have i₁ := b1e340511
           have i₂ := b1e227369
           grind)
        | exact superpose b1e227369 b1e340511
        | exact resolve b1e340511 b1e227369
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e340511
      have b1e340823 : (M.op (σ y) (σ x)) = (σ (k x x)) ∨ x = y := by grind
      clear b1e340822
      have b1e346105 : (σ y) ≠ (σ (k x x)) ∨ x = y := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e340823
           grind)
        | exact superpose b1e340823 b1e18
        | exact resolve b1e18 b1e340823
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e340823
      have b1e347410 : (σ y) ≠ (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e346105
           have i₂ := b1e13713 x x
           grind)
        | exact superpose b1e13713 b1e346105
        | (have j1 := b1e13713 x x
           grind)
        | exact resolve b1e346105 b1e13713
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13713 b1e346105
      have b1e347411 : (σ y) ≠ (σ y) ∨ x = y ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e347410
           have i₂ := b1e227369
           grind)
        | exact superpose b1e227369 b1e347410
        | exact resolve b1e347410 b1e227369
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e347410
      have b1e347412 : x = y ∨ x = (M.op x x) := by grind
      clear b1e347411
      have b1e347417 : x = y ∨ x = y := by
        first
        | (have i₁ := b1e347412
           have i₂ := b1e227369
           grind)
        | exact superpose b1e227369 b1e347412
        | exact resolve b1e347412 b1e227369
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e227369 b1e347412
      have b1e347418 : x = y := by grind
      clear b1e347417
      have b1e348709 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e1011
           have i₂ := b1e347418
           grind)
        | exact superpose b1e347418 b1e1011
        | exact resolve b1e1011 b1e347418
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1011 b1e347418
      have b1e348795 : False := by grind
      exact b1e348795
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b2e17 : y ≠ (M.op y x) := by grind
      have b2e18 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e19 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
      have b2e20 : (σ x) = (k (σ x) (σ y)) := by grind
      clear b2e19
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
      have b2e23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X1 (τ X0)
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
      have b2e30 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
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
      have b2e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X2 X1 X3
           have i₂ := b2e10 X2 X1 X0
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e34 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b2e10 X0 (σ x) (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X3 (M.op X1 X2) X2
           have i₂ := b2e10 X2 X1 X0
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e36 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 X2 X0 (M.op x X1)
           have i₂ := b2e10 X0 X1 x
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e42 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e11 (k (τ X0) X1)
           have i₂ := b2e22 X0 X1
           grind)
        | exact superpose b2e22 b2e11
        | exact resolve b2e11 b2e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
      have b2e46 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e22 X0 X1
           have i₂ := b2e14 (τ X0) X1
           grind)
        | exact superpose b2e14 b2e22
        | (have j1 := b2e14 (τ X0) X1
           grind)
        | exact resolve b2e22 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e47 : x = (M.op x y) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b2e27
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e27
        | (have j1 := b2e14 y x
           grind)
        | exact resolve b2e27 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27
      have b2e48 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
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
      have b2e49 : (σ (M.op x y)) = (σ x) := by
        first
        | (have r₁ := b2e48
           have r₂ := b2e17
           grind)
        | exact resolve b2e48 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e48
      have b2e50 : x = (M.op x y) := by
        first
        | (have r₁ := b2e47
           have r₂ := b2e17
           grind)
        | exact resolve b2e47 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47
      have b2e52 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b2e10 X0 y x
           have i₂ := b2e50
           grind)
        | exact superpose b2e50 b2e10
        | exact resolve b2e10 b2e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e61 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e11 (k X0 (τ X1))
           have i₂ := b2e23 X1 X0
           grind)
        | exact superpose b2e23 b2e11
        | exact resolve b2e11 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e80 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e33 X0 (σ x) X1 (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e33
        | exact resolve b2e33 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e81 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e33 X0 y X1 x
           have i₂ := b2e50
           grind)
        | exact superpose b2e50 b2e33
        | exact resolve b2e33 b2e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e94 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X1) ∨ (k X2 (M.op X3 X1)) = X2 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e13 X2 (M.op X3 X1)
           have i₂ := b2e33 X3 X1 X2 X0
           grind)
        | (have i₁ := b2e13 X2 (M.op X3 X1)
           have i₂ := b2e33 X0 X1 X2 X3
           grind)
        | exact superpose b2e33 b2e13
        | (have j0 := b2e13 X2 (M.op X3 X1)
           grind)
        | (have r₁ := b2e13 X2 (M.op (M.op X3 X2) X2)
           have r₂ := b2e33 (M.op X3 X2) X2 X2 X3
           grind)
        | (have r₁ := b2e13 X2 (M.op (M.op X0 X2) X2)
           have r₂ := b2e33 X0 X2 X2 (M.op X0 X2)
           grind)
        | exact resolve b2e13 b2e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e109 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op (σ x) X0)) X1) = (M.op (M.op (σ y) X0) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e33 X0 (M.op (σ x) X0) X1 X2
           have i₂ := b2e34 X0
           grind)
        | exact superpose b2e34 b2e33
        | exact resolve b2e33 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e33
      have b2e200 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
        intro X0
        first
        | (have i₁ := b2e36 (σ x) (M.op x (σ y)) X0
           have i₂ := b2e30 x
           grind)
        | exact superpose b2e30 b2e36
        | exact resolve b2e36 b2e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e203 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op (M.op y x) X0) := by
        intro X0
        first
        | (have i₁ := b2e36 y x X0
           have i₂ := b2e50
           grind)
        | exact superpose b2e50 b2e36
        | exact resolve b2e36 b2e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e227 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 X0 (M.op X2 X1) X1
           have i₂ := b2e36 X1 X2 X0
           grind)
        | exact superpose b2e36 b2e10
        | exact resolve b2e10 b2e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e36
      have b2e237 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y x) X0) := by
        intro X0
        first
        | (have i₁ := b2e203 X0
           have i₂ := b2e52 X0
           grind)
        | exact superpose b2e52 b2e203
        | exact resolve b2e203 b2e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e203
      have b2e239 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (M.op (σ y) (σ y)) X0) := by
        intro X0
        first
        | (have i₁ := b2e200 X0
           have i₂ := b2e109 (σ y) X0 (σ x)
           grind)
        | exact superpose b2e109 b2e200
        | exact resolve b2e200 b2e109
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e109 b2e200
      have b2e244 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ y) (σ y)) X0) := by
        intro X0
        first
        | (have i₁ := b2e239 X0
           have i₂ := b2e34 X0
           grind)
        | exact superpose b2e34 b2e239
        | exact resolve b2e239 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34 b2e239
      have b2e254 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b2e10 X0 x y
           have i₂ := b2e237 X0
           grind)
        | exact superpose b2e237 b2e10
        | exact resolve b2e10 b2e237
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e237
      have b2e468 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ y)) (σ x)) X0) = (M.op X0 (M.op (σ y) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e35 X1 (σ y) (σ x) X0
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e35
        | exact resolve b2e35 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e569 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (M.op X0 X1) (σ y))) (σ x)) := by
        intro X0 X1
        first
        | (have i₁ := b2e30 (M.op (M.op x X0) X1)
           have i₂ := b2e35 x X0 X1 (σ y)
           grind)
        | exact superpose b2e35 b2e30
        | exact resolve b2e30 b2e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e35
      have b2e571 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op X0 X1) (σ y)) (σ x))) := by
        intro X0 X1
        first
        | (have i₁ := b2e569 X0 X1
           have i₂ := b2e10 (σ x) (M.op (M.op X0 X1) (σ y)) (σ y)
           grind)
        | exact superpose b2e10 b2e569
        | exact resolve b2e569 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e569
      have b2e607 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b2e468 X0 x
           have i₂ := b2e80 (M.op x (σ y)) X0
           grind)
        | exact superpose b2e80 b2e468
        | exact resolve b2e468 b2e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e80 b2e468
      have b2e613 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
        first
        | (have i₁ := b2e571 x x
           have i₂ := b2e227 (σ x) (σ y) (M.op x x)
           grind)
        | exact superpose b2e227 b2e571
        | exact resolve b2e571 b2e227
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e227 b2e571
      have b2e626 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e613
           have i₂ := b2e607 (σ x)
           grind)
        | exact superpose b2e607 b2e613
        | exact resolve b2e613 b2e607
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e607 b2e613
      have b2e629 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b2e626
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e626
        | exact resolve b2e626 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e626
      have b2e630 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e629
           grind)
        | exact superpose b2e629 b2e16
        | exact resolve b2e16 b2e629
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e644 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e630
           have i₂ := b2e49
           grind)
        | exact superpose b2e49 b2e630
        | exact resolve b2e630 b2e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e630
      have b2e1049 : x = (M.op y x) := by
        first
        | (have i₁ := b2e254 y
           have i₂ := b2e50
           grind)
        | exact superpose b2e50 b2e254
        | exact resolve b2e254 b2e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1130 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e45 X1 X0
           have i₂ := b2e45 X0 X1
           grind)
        | exact superpose b2e45 b2e45
        | (have j0 := b2e45 X1 X0
           have j1 := b2e45 X1 X0
           grind)
        | exact resolve b2e45 b2e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1137 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e13 (σ X1) (σ X0)
           have i₂ := b2e45 X0 X1
           grind)
        | exact superpose b2e45 b2e13
        | (have j0 := b2e13 (σ X1) (σ X0)
           have j1 := b2e45 X0 X1
           grind)
        | (have r₁ := b2e13 (σ X0) (σ X1)
           have r₂ := b2e45 X0 X1
           grind)
        | exact resolve b2e13 b2e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1158 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e13 (σ X1) (σ X0)
           have i₂ := b2e45 X1 X0
           grind)
        | exact superpose b2e45 b2e13
        | (have j0 := b2e13 (σ X1) (σ X0)
           have j1 := b2e45 X1 X0
           grind)
        | (have r₁ := b2e13 (σ X0) (σ X1)
           have r₂ := b2e45 X0 X1
           grind)
        | exact resolve b2e13 b2e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1174 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b2e1158 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1158
      have b2e1176 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e1174 X0 X1
           have i₂ := b2e15 X1 X0
           grind)
        | exact superpose b2e15 b2e1174
        | (have j0 := b2e1174 X0 X1
           grind)
        | exact resolve b2e1174 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1174
      have b2e1181 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e1137 X0 X1
           have i₂ := b2e15 X1 X0
           grind)
        | exact superpose b2e15 b2e1137
        | (have j0 := b2e1137 X0 X1
           grind)
        | exact resolve b2e1137 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1137
      have b2e1199 : x ≠ y := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e1049
           grind)
        | exact superpose b2e1049 b2e17
        | exact resolve b2e17 b2e1049
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1049
      have b2e1216 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e42 X1 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e42
        | exact resolve b2e42 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e42
      have b2e16421 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e46 (σ X0) X1
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e46
        | exact resolve b2e46 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46
      have b2e16475 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e16421 X0 X1
           have i₂ := b2e15 X0 X1
           grind)
        | exact superpose b2e15 b2e16421
        | (have j0 := b2e16421 X0 X1
           grind)
        | exact resolve b2e16421 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16421
      have b2e16884 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X0) X0)) = X0 := by
        intro X0 X1
        first
        | (have j0 := b2e94 X0 X0 X0 (M.op X1 X0)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e94
      have b2e17040 : (σ y) = (k (σ y) (M.op (σ y) (σ y))) := by
        first
        | (have i₁ := b2e16884 (σ y) (σ y)
           have i₂ := b2e244 (σ y)
           grind)
        | exact superpose b2e244 b2e16884
        | exact resolve b2e16884 b2e244
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e244 b2e16884
      have b2e19326 : (k y (τ (M.op (σ y) (σ y)))) = (τ (σ y)) := by
        first
        | (have i₁ := b2e61 y (M.op (σ y) (σ y))
           have i₂ := b2e17040
           grind)
        | exact superpose b2e17040 b2e61
        | exact resolve b2e61 b2e17040
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e17040
      have b2e19328 : y = (k y (τ (M.op (σ y) (σ y)))) := by
        first
        | (have i₁ := b2e19326
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e19326
        | exact resolve b2e19326 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19326
      have b2e33894 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e1176 X0 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e1176
        | exact resolve b2e1176 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1176
      have b2e34039 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e33894 X0 X1
           have i₂ := b2e22 X0 X1
           grind)
        | exact superpose b2e22 b2e33894
        | (have j0 := b2e33894 X0 X1
           grind)
        | exact resolve b2e33894 b2e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e33894
      have b2e34045 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e34039 X0 X1
           have i₂ := b2e22 X0 X1
           grind)
        | exact superpose b2e22 b2e34039
        | (have j0 := b2e34039 X0 X1
           grind)
        | exact resolve b2e34039 b2e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34039
      have b2e87791 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e34045 X0 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e34045
        | exact resolve b2e34045 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34045
      have b2e92042 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b2e87791 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e87791
      have b2e103001 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e1181 (τ X0) (τ X1)
           have i₂ := b2e1216 X1 X0
           grind)
        | exact superpose b2e1216 b2e1181
        | (have j0 := b2e1181 (τ X0) (τ X1)
           grind)
        | exact resolve b2e1181 b2e1216
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1181 b2e1216
      have b2e103039 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e103001 X0 X1
           have i₂ := b2e12 (k X0 X1)
           grind)
        | exact superpose b2e12 b2e103001
        | (have j0 := b2e103001 X0 X1
           grind)
        | exact resolve b2e103001 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e103001
      have b2e103049 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e103039 X0 X1
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e103039
        | (have j0 := b2e103039 X0 X1
           grind)
        | exact resolve b2e103039 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e103039
      have b2e103056 : ∀ X0 X1 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e103049 X0 X1
           have i₂ := b2e23 X0 (τ X1)
           grind)
        | exact superpose b2e23 b2e103049
        | (have j0 := b2e103049 X0 X1
           grind)
        | exact resolve b2e103049 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e103049
      have b2e103062 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e103056 X0 X0
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e103056
        | (have j0 := b2e103056 X0 X1
           grind)
        | exact resolve b2e103056 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e103056
      have b2e103063 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e103062 X0 X1
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e103062
        | (have j0 := b2e103062 X0 X1
           grind)
        | exact resolve b2e103062 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e103062
      have b2e103064 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e103063 X0 X0
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e103063
        | (have j0 := b2e103063 X0 X1
           grind)
        | exact resolve b2e103063 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e103063
      have b2e103065 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b2e103064 X0 X1
           have j1 := b2e92042 X1 X0
           grind)
        | (have r₁ := b2e103064 X1 X0
           have r₂ := b2e92042 X0 X1
           grind)
        | (have r₁ := b2e103064 X0 X1
           have r₂ := b2e92042 X0 X1
           grind)
        | exact resolve b2e103064 b2e92042
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e92042 b2e103064
      have b2e103083 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e103065 (σ X0) (σ X1)
           have i₂ := b2e15 X0 X1
           grind)
        | exact superpose b2e15 b2e103065
        | (have j0 := b2e103065 (σ X0) (σ X1)
           grind)
        | exact resolve b2e103065 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e103120 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e103083 X0 X1
           have i₂ := b2e15 X1 X0
           grind)
        | exact superpose b2e15 b2e103083
        | (have j0 := b2e103083 X0 X1
           grind)
        | exact resolve b2e103083 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e103083
      have b2e216309 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e1130 (τ X0) X1
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e1130
        | exact resolve b2e1130 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1130
      have b2e216620 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e216309 X0 X1
           have i₂ := b2e23 X0 X1
           grind)
        | exact superpose b2e23 b2e216309
        | (have j0 := b2e216309 X0 X1
           grind)
        | exact resolve b2e216309 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e23 b2e216309
      have b2e216633 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e216620 X0 X1
           have i₂ := b2e22 X0 X1
           grind)
        | exact superpose b2e22 b2e216620
        | (have j0 := b2e216620 X0 X1
           grind)
        | exact resolve b2e216620 b2e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e22 b2e216620
      have b2e216638 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
        intro X0 X1
        first
        | (have j0 := b2e216633 X0 X1
           have j1 := b2e13 X0 (σ X1)
           grind)
        | (have r₁ := b2e216633 X0 X1
           have r₂ := b2e13 X0 (σ X1)
           grind)
        | exact resolve b2e216633 b2e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e216633
      have b2e216806 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e216638 X0 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e216638
        | exact resolve b2e216638 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e216834 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e61 X0 (σ X1)
           have i₂ := b2e216638 (σ X0) X1
           grind)
        | exact superpose b2e216638 b2e61
        | (have j1 := b2e216638 (σ X0) X1
           grind)
        | exact resolve b2e61 b2e216638
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e61 b2e216638
      have b2e216898 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e216834 X0 X1
           have i₂ := b2e11 X1
           grind)
        | exact superpose b2e11 b2e216834
        | (have j0 := b2e216834 X0 X1
           grind)
        | exact resolve b2e216834 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e216834
      have b2e216921 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e216898 X0 X1
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e216898
        | (have j0 := b2e216898 X0 X1
           grind)
        | exact resolve b2e216898 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e216898
      have b2e216929 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e216921 X0 X1
           have i₂ := b2e15 X1 X0
           grind)
        | exact superpose b2e15 b2e216921
        | (have j0 := b2e216921 X0 X1
           grind)
        | exact resolve b2e216921 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e216921
      have b2e217911 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e103120 X0 X1
           have i₂ := b2e216806 X1 X0
           grind)
        | exact superpose b2e216806 b2e103120
        | (have j0 := b2e103120 X0 X1
           have j1 := b2e216806 X1 X0
           grind)
        | exact resolve b2e103120 b2e216806
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e217942 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b2e217911 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e217911
      have b2e218252 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (σ (k X1 X0)) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e103120 X0 X1
           have i₂ := b2e217942 X1 X0
           grind)
        | exact superpose b2e217942 b2e103120
        | (have j0 := b2e103120 X0 X1
           have j1 := b2e217942 X0 X1
           grind)
        | (have r₁ := b2e103120 X1 X0
           have r₂ := b2e217942 X0 X1
           grind)
        | exact resolve b2e103120 b2e217942
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e103120 b2e217942
      have b2e218304 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b2e218252 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e218252
      have b2e222072 : y = (k y (τ (σ (k y y)))) ∨ y = (k y y) := by
        first
        | (have i₁ := b2e19328
           have i₂ := b2e216929 y y
           grind)
        | exact superpose b2e216929 b2e19328
        | (have j1 := b2e216929 y (τ (σ (k y y)))
           grind)
        | exact resolve b2e19328 b2e216929
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19328
      have b2e222111 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (k X0 y)) (σ x)) ∨ y = (k y X0) := by
        intro X0
        first
        | (have i₁ := b2e30 (σ X0)
           have i₂ := b2e216929 y X0
           grind)
        | exact superpose b2e216929 b2e30
        | (have j1 := b2e216929 y X0
           grind)
        | exact resolve b2e30 b2e216929
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e30 b2e216929
      have b2e222271 : ∀ X0 : G, (σ y) = (M.op (σ (k X0 y)) (σ x)) ∨ y = (k y X0) := by
        intro X0
        first
        | (have i₁ := b2e222111 X0
           have i₂ := b2e629
           grind)
        | exact superpose b2e629 b2e222111
        | (have j0 := b2e222111 X0
           grind)
        | exact resolve b2e222111 b2e629
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e629 b2e222111
      have b2e222278 : y = (k y (k y y)) ∨ y = (k y y) := by
        first
        | (have i₁ := b2e222072
           have i₂ := b2e11 (k y y)
           grind)
        | exact superpose b2e11 b2e222072
        | exact resolve b2e222072 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e222072
      have b2e223598 : y = (k y (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e222278
           have i₂ := b2e14 y y
           grind)
        | exact superpose b2e14 b2e222278
        | (have j1 := b2e14 y y
           grind)
        | exact resolve b2e222278 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e222278
      have b2e223609 : y = (k y (M.op y y)) ∨ y = (M.op y y) := by grind
      clear b2e223598
      have b2e224223 : y ≠ y ∨ (M.op y y) = (k (M.op y y) y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e103065 y (M.op y y)
           have i₂ := b2e223609
           grind)
        | exact superpose b2e223609 b2e103065
        | (have j0 := b2e103065 y (M.op y y)
           grind)
        | (have r₁ := b2e103065 y (M.op y y)
           have r₂ := b2e223609
           grind)
        | exact resolve b2e103065 b2e223609
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e103065 b2e223609
      have b2e224228 : (M.op y y) = (k (M.op y y) y) ∨ y = (M.op y y) := by grind
      clear b2e224223
      have b2e235053 : (σ (M.op y y)) = (σ (M.op (M.op y y) y)) ∨ y = (M.op y (M.op y y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e16475 (M.op y y) y
           have i₂ := b2e224228
           grind)
        | exact superpose b2e224228 b2e16475
        | (have j0 := b2e16475 (M.op y y) y
           grind)
        | exact resolve b2e16475 b2e224228
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16475 b2e224228
      have b2e235061 : (σ (M.op y y)) = (σ (M.op y (M.op y y))) ∨ y = (M.op y (M.op y y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e235053
           have i₂ := b2e10 y y y
           grind)
        | exact superpose b2e10 b2e235053
        | exact resolve b2e235053 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e235053
      have b2e235067 : (σ (M.op x y)) = (σ (M.op y y)) ∨ y = (M.op y (M.op y y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e235061
           have i₂ := b2e52 y
           grind)
        | exact superpose b2e52 b2e235061
        | exact resolve b2e235061 b2e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e235061
      have b2e235070 : (σ x) = (σ (M.op y y)) ∨ y = (M.op y (M.op y y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e235067
           have i₂ := b2e49
           grind)
        | exact superpose b2e49 b2e235067
        | exact resolve b2e235067 b2e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e49 b2e235067
      have b2e235073 : y = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e235070
           have i₂ := b2e52 y
           grind)
        | exact superpose b2e52 b2e235070
        | exact resolve b2e235070 b2e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e52 b2e235070
      have b2e235074 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e235073
           have i₂ := b2e50
           grind)
        | exact superpose b2e50 b2e235073
        | exact resolve b2e235073 b2e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e235073
      have b2e235075 : (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) := by
        first
        | (have r₁ := b2e235074
           have r₂ := b2e1199
           grind)
        | exact resolve b2e235074 b2e1199
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e235074
      have b2e246468 : ∀ X0 : G, (σ y) = (M.op (σ (M.op X0 y)) (σ x)) ∨ y = (k y X0) ∨ y = (k y X0) := by
        intro X0
        first
        | (have i₁ := b2e222271 X0
           have i₂ := b2e216806 X0 y
           grind)
        | exact superpose b2e216806 b2e222271
        | (have j0 := b2e222271 X0
           have j1 := b2e216806 X0 y
           grind)
        | exact resolve b2e222271 b2e216806
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e216806 b2e222271
      have b2e246627 : ∀ X0 : G, (σ y) = (M.op (σ (M.op X0 y)) (σ x)) ∨ y = (k y X0) := by
        intro X0
        first
        | (have j0 := b2e246468 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e246468
      have b2e258533 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e246627 y
           have i₂ := b2e235075
           grind)
        | exact superpose b2e235075 b2e246627
        | (have j0 := b2e246627 y
           grind)
        | exact resolve b2e246627 b2e235075
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e235075 b2e246627
      have b2e258759 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) := by
        first
        | (have j1 := b2e13 y y
           grind)
        | (have r₁ := b2e258533
           have r₂ := b2e13 y y
           grind)
        | exact resolve b2e258533 b2e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e258533
      have b2e261521 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ y = (k y y) := by
        first
        | (have i₁ := b2e45 x x
           have i₂ := b2e258759
           grind)
        | exact superpose b2e258759 b2e45
        | exact resolve b2e45 b2e258759
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e45 b2e258759
      have b2e261752 : (σ y) = (σ (k x x)) ∨ y = (k y y) := by
        first
        | (have r₁ := b2e261521
           have r₂ := b2e644
           grind)
        | exact resolve b2e261521 b2e644
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e261521
      have b2e264450 : (k x x) = (τ (σ y)) ∨ y = (k y y) := by
        first
        | (have i₁ := b2e11 (k x x)
           have i₂ := b2e261752
           grind)
        | exact superpose b2e261752 b2e11
        | exact resolve b2e11 b2e261752
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e261752
      have b2e264509 : y = (k x x) ∨ y = (k y y) := by
        first
        | (have i₁ := b2e264450
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e264450
        | exact resolve b2e264450 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e264450
      have b2e267267 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (k y y) := by
        first
        | (have i₁ := b2e218304 x x
           have i₂ := b2e264509
           grind)
        | exact superpose b2e264509 b2e218304
        | exact resolve b2e218304 b2e264509
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e218304 b2e264509
      have b2e267269 : y = (k y y) ∨ y = (M.op x x) := by
        first
        | (have r₁ := b2e267267
           have r₂ := b2e644
           grind)
        | exact resolve b2e267267 b2e644
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e644 b2e267267
      have b2e269973 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b2e14 y y
           have i₂ := b2e267269
           grind)
        | exact superpose b2e267269 b2e14
        | (have j0 := b2e14 y y
           grind)
        | exact resolve b2e14 b2e267269
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e267269
      have b2e269977 : y = (M.op x x) ∨ y = (M.op y y) := by grind
      clear b2e269973
      have b2e272620 : y = (M.op x y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e254 x
           have i₂ := b2e269977
           grind)
        | exact superpose b2e269977 b2e254
        | exact resolve b2e254 b2e269977
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e254 b2e269977
      have b2e272894 : x = y ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e272620
           have i₂ := b2e50
           grind)
        | exact superpose b2e50 b2e272620
        | exact resolve b2e272620 b2e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e272620
      have b2e272952 : y = (M.op y y) := by
        first
        | (have r₁ := b2e272894
           have r₂ := b2e1199
           grind)
        | exact resolve b2e272894 b2e1199
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e272894
      have b2e276145 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b2e81 y X0
           have i₂ := b2e272952
           grind)
        | exact superpose b2e272952 b2e81
        | exact resolve b2e81 b2e272952
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e81
      have b2e279056 : x = (M.op y y) := by
        first
        | (have i₁ := b2e50
           have i₂ := b2e276145 y
           grind)
        | exact superpose b2e276145 b2e50
        | exact resolve b2e50 b2e276145
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50 b2e276145
      have b2e279538 : x = y := by
        first
        | (have i₁ := b2e279056
           have i₂ := b2e272952
           grind)
        | exact superpose b2e272952 b2e279056
        | exact resolve b2e279056 b2e272952
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e272952 b2e279056
      have b2e279628 : False := by grind
      exact b2e279628
    · have b3e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op y x) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e33 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X0 X1
           have i₂ := b3e14 (σ X0) (σ X1)
           grind)
        | exact superpose b3e14 b3e15
        | (have j1 := b3e14 (σ X0) (σ X1)
           grind)
        | exact resolve b3e15 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1007 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e33 x y
           grind)
        | exact superpose b3e33 b3e16
        | (have j1 := b3e33 x y
           grind)
        | exact resolve b3e16 b3e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e33
      have b3e1061 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have r₁ := b3e1007
           have r₂ := b3e18
           grind)
        | exact resolve b3e1007 b3e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1007
      have b3e1066 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b3e1061
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e1061
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e1061 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1061
      have b3e1067 : y = (M.op y x) := by grind
      clear b3e1066
      have b3e1068 : False := by grind
      exact b3e1068

/-- `Equation4460`: `x ◇ (y ◇ x) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation4460 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4460 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4460.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X0) := by
        intro X0 X1 X2
        grind
      have b0e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
      have b0e33 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ x) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e33 X0 x
           have i₂ := b0e34 X0 x
           grind)
        | exact superpose b0e34 b0e33
        | exact resolve b0e33 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e39 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e36 (σ y)
           grind)
        | exact superpose b0e36 b0e16
        | exact resolve b0e16 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e50 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (k X0 X3) = (M.op X0 X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X1 X2 X3
           have i₂ := b0e14 X0 X3
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 (M.op X2 X2) X1
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X0 X3
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e52 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) X1) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 X1 X2
           have i₂ := b0e14 X0 X1
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 (M.op X1 X0) X1
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X0 X1
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
      have b0e58 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op x X1) ∨ (k X0 X3) = (M.op X0 X3) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e50 X0 X1 x X3
           have i₂ := b0e34 X1 x
           grind)
        | exact superpose b0e34 b0e50
        | (have j0 := b0e50 X0 X1 x X3
           grind)
        | exact resolve b0e50 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50
      have b0e59 : ∀ X0 X1 : G, (M.op x (M.op X1 X0)) = (M.op (M.op X1 X0) (M.op x X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e34 (M.op X1 X0) X0
           have i₂ := b0e34 X0 X1
           grind)
        | exact superpose b0e34 b0e34
        | exact resolve b0e34 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e63 : (M.op (σ y) (σ x)) = (M.op x (σ y)) := by
        first
        | (have i₁ := b0e34 (σ y) (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e34
        | exact resolve b0e34 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e65 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e34 y y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e34
        | exact resolve b0e34 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e68 : ∀ X0 X2 : G, (M.op (M.op X2 X2) X0) = (M.op x X0) := by
        intro X0 X2
        first
        | (have i₁ := b0e10 X0 x X2
           have i₂ := b0e34 X0 x
           grind)
        | exact superpose b0e34 b0e10
        | exact resolve b0e10 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e161 : (M.op x (σ y)) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b0e39
           have i₂ := b0e65
           grind)
        | exact superpose b0e65 b0e39
        | exact resolve b0e39 b0e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e65
      have b0e356 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e51 (σ X0) (σ X1)
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e51
        | exact resolve b0e51 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e362 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e51 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51
      have b0e520 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X0 X0) x) ∨ (k X1 X3) = (M.op X1 X3) ∨ (M.op X2 x) = (k X2 x) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e58 X1 X2 X3
           have i₂ := b0e52 X2 x X0
           grind)
        | exact superpose b0e52 b0e58
        | (have j0 := b0e58 X1 X1 X3
           have j1 := b0e52 X1 X3 X2
           grind)
        | exact resolve b0e58 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52 b0e58
      have b0e568 : ∀ X1 X2 X3 : G, (M.op X1 X2) = (M.op x x) ∨ (k X1 X3) = (M.op X1 X3) ∨ (M.op X2 x) = (k X2 x) := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e520 x X1 X2 X3
           have i₂ := b0e68 x x
           grind)
        | exact superpose b0e68 b0e520
        | (have j0 := b0e520 x X1 X2 X3
           grind)
        | exact resolve b0e520 b0e68
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68 b0e520
      have b0e1156 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op x (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e36 (σ x)
           have i₂ := b0e55 X0 x
           grind)
        | exact superpose b0e55 b0e36
        | (have j1 := b0e55 X0 x
           grind)
        | exact resolve b0e36 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e55
      have b0e5965 : (M.op x (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
        first
        | (have i₁ := b0e63
           have i₂ := b0e356 y x
           grind)
        | exact superpose b0e356 b0e63
        | (have j1 := b0e356 y x
           grind)
        | exact resolve b0e63 b0e356
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e356
      have b0e7004 : (M.op x (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op x (σ x)) := by
        first
        | (have i₁ := b0e63
           have i₂ := b0e1156 y
           grind)
        | exact superpose b0e1156 b0e63
        | (have j1 := b0e1156 y
           grind)
        | exact resolve b0e63 b0e1156
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63 b0e1156
      have b0e16429 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 X0) = (M.op x x) ∨ (M.op X0 x) = (k X0 x) := by
        intro X0
        first
        | (have j0 := b0e568 X0 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e568
      have b0e16430 : ∀ X0 : G, (M.op X0 X0) = (M.op x x) ∨ (M.op X0 x) = (k X0 x) := by
        intro X0
        first
        | (have j0 := b0e16429 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16429
      have b0e24313 : ∀ X0 : G, (M.op x x) ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 x) = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b0e362 X0 X0
           have i₂ := b0e16430 X0
           grind)
        | (have i₁ := b0e362 x x
           have i₂ := b0e16430 X0
           grind)
        | exact superpose b0e16430 b0e362
        | (have j0 := b0e362 X0 X0
           have j1 := b0e16430 X0
           grind)
        | (have r₁ := b0e362 (M.op x x) (M.op x x)
           have r₂ := b0e16430 (M.op x x)
           grind)
        | exact resolve b0e362 b0e16430
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16430
      have b0e24515 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 x) = (k X0 x) := by
        intro X0
        first
        | (have j0 := b0e24313 X0
           have j1 := b0e14 X0 x
           grind)
        | (have r₁ := b0e24313 X0
           have r₂ := b0e14 X0 x
           grind)
        | (have r₁ := b0e24313 (M.op x x)
           have r₂ := b0e14 (M.op x x) x
           grind)
        | (have r₁ := b0e24313 (k x x)
           have r₂ := b0e14 x x
           grind)
        | exact resolve b0e24313 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24313
      have b0e25062 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 x) = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 X0
           have i₂ := b0e24515 X0
           grind)
        | exact superpose b0e24515 b0e14
        | (have j0 := b0e14 X0 X0
           have j1 := b0e24515 X0
           grind)
        | exact resolve b0e14 b0e24515
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24515
      have b0e25126 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 x) = (k X0 x) := by
        intro X0
        first
        | (have j0 := b0e25062 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25062
      have b0e60299 : (M.op x (σ y)) = (σ (M.op y x)) ∨ (σ x) = (σ (M.op y x)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e5965
           have i₂ := b0e25126 y
           grind)
        | exact superpose b0e25126 b0e5965
        | (have j1 := b0e25126 y
           grind)
        | exact resolve b0e5965 b0e25126
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5965 b0e25126
      have b0e60351 : (σ x) = (σ (M.op y x)) ∨ y = (M.op y y) := by
        first
        | (have r₁ := b0e60299
           have r₂ := b0e161
           grind)
        | exact resolve b0e60299 b0e161
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60299
      have b0e60356 : (σ x) = (σ (M.op y x)) ∨ x = y := by
        first
        | (have i₁ := b0e60351
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e60351
        | exact resolve b0e60351 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60351
      have b0e60358 : (σ x) ≠ (M.op x (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e161
           have i₂ := b0e60356
           grind)
        | exact superpose b0e60356 b0e161
        | exact resolve b0e161 b0e60356
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e161
      have b0e60359 : (M.op y x) = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e11 (M.op y x)
           have i₂ := b0e60356
           grind)
        | exact superpose b0e60356 b0e11
        | exact resolve b0e11 b0e60356
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60356
      have b0e60444 : x = (M.op y x) ∨ x = y := by
        first
        | (have i₁ := b0e60359
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e60359
        | exact resolve b0e60359 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60359
      have b0e60533 : x ≠ x ∨ x = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e362 y x
           have i₂ := b0e60444
           grind)
        | exact superpose b0e60444 b0e362
        | (have j0 := b0e362 y x
           grind)
        | (have r₁ := b0e362 y x
           have r₂ := b0e60444
           grind)
        | exact resolve b0e362 b0e60444
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e362 b0e60444
      have b0e60548 : x = (k y x) ∨ x = y := by grind
      clear b0e60533
      have b0e61306 : (σ x) = (M.op x (σ y)) ∨ (σ y) = (M.op x (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e7004
           have i₂ := b0e60548
           grind)
        | exact superpose b0e60548 b0e7004
        | exact resolve b0e7004 b0e60548
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7004 b0e60548
      have b0e61376 : (σ y) = (M.op x (σ x)) ∨ x = y := by
        first
        | (have r₁ := b0e61306
           have r₂ := b0e60358
           grind)
        | exact resolve b0e61306 b0e60358
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61306
      have b0e63132 : (M.op (σ y) (σ y)) = (M.op x (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e59 (σ x) x
           have i₂ := b0e61376
           grind)
        | exact superpose b0e61376 b0e59
        | exact resolve b0e59 b0e61376
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59 b0e61376
      have b0e63167 : (σ x) = (M.op x (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e63132
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e63132
        | exact resolve b0e63132 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63132
      have b0e63206 : x = y := by
        first
        | (have r₁ := b0e63167
           have r₂ := b0e60358
           grind)
        | exact resolve b0e63167 b0e60358
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60358 b0e63167
      have b0e63343 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e63206
           grind)
        | exact superpose b0e63206 b0e16
        | exact resolve b0e16 b0e63206
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63206
      have b0e63555 : (σ x) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e63343
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e63343
        | exact resolve b0e63343 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63343
      have b0e63597 : False := by grind
      exact b0e63597
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X0) := by
        intro X0 X1 X2
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
      have b1e30 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 X1 y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e33 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b1e30 y y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e30
        | exact resolve b1e30 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e46 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b1e49 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
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
      have b1e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
      have b1e281 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
        intro X0
        grind
      clear b1e26
      have b1e287 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b1e281 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e281
        | exact resolve b1e281 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e281
      have b1e295 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b1e46 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e46
      have b1e312 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b1e49 (σ x)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e49
      have b1e313 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e312
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e312
        | exact resolve b1e312 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e312
      have b1e314 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e313
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e313
        | exact resolve b1e313 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e313
      have b1e315 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e314
           grind)
        | exact superpose b1e314 b1e16
        | exact resolve b1e16 b1e314
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e318 : (M.op (σ y) (σ y)) = (M.op x (σ y)) := by
        first
        | (have i₁ := b1e30 (σ y) (σ x)
           have i₂ := b1e314
           grind)
        | exact superpose b1e314 b1e30
        | exact resolve b1e30 b1e314
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30 b1e314
      have b1e323 : (σ y) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b1e315
           have i₂ := b1e33
           grind)
        | exact superpose b1e33 b1e315
        | exact resolve b1e315 b1e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e33 b1e315
      have b1e727 : x ≠ y ∨ y = (k y y) := by
        first
        | (have i₁ := b1e295 y y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e295
        | (have j0 := b1e295 y y
           grind)
        | exact resolve b1e295 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e295
      have b1e767 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e50 y y
           grind)
        | exact superpose b1e50 b1e18
        | (have j1 := b1e50 y y
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e50 x y
           grind)
        | exact resolve b1e18 b1e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e50
      have b1e838 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op x (σ y)) := by
        first
        | (have i₁ := b1e767
           have i₂ := b1e318
           grind)
        | exact superpose b1e318 b1e767
        | exact resolve b1e767 b1e318
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e767
      have b1e1116 : y = (k (τ (M.op x (σ y))) y) := by
        first
        | (have i₁ := b1e287 y
           have i₂ := b1e318
           grind)
        | exact superpose b1e318 b1e287
        | exact resolve b1e287 b1e318
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e287 b1e318
      have b1e1177 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op x (σ y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e838
           have i₂ := b1e14 y y
           grind)
        | exact superpose b1e14 b1e838
        | (have j1 := b1e14 y y
           grind)
        | exact resolve b1e838 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e838
      have b1e1193 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op x (σ y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e1177
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1177
        | exact resolve b1e1177 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1177
      have b1e1194 : (σ y) = (M.op x (σ y)) ∨ y = (M.op y y) := by grind
      clear b1e1193
      have b1e1195 : (σ y) = (M.op x (σ y)) ∨ x = y := by
        first
        | (have i₁ := b1e1194
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1194
        | exact resolve b1e1194 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1194
      have b1e1266 : y = (k (τ (σ y)) y) ∨ x = y := by
        first
        | (have i₁ := b1e1116
           have i₂ := b1e1195
           grind)
        | exact superpose b1e1195 b1e1116
        | exact resolve b1e1116 b1e1195
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1116 b1e1195
      have b1e1287 : y = (k y y) ∨ x = y := by
        first
        | (have i₁ := b1e1266
           have i₂ := b1e11 y
           grind)
        | exact superpose b1e11 b1e1266
        | exact resolve b1e1266 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1266
      have b1e1288 : y = (k y y) := by
        first
        | (have r₁ := b1e1287
           have r₂ := b1e727
           grind)
        | exact resolve b1e1287 b1e727
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e727 b1e1287
      have b1e1346 : y = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e14 y y
           have i₂ := b1e1288
           grind)
        | exact superpose b1e1288 b1e14
        | (have j0 := b1e14 y y
           grind)
        | exact resolve b1e14 b1e1288
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1288
      have b1e1351 : y = (M.op y y) := by grind
      clear b1e1346
      have b1e1624 : x = y := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e1351
           grind)
        | exact superpose b1e1351 b1e17
        | exact resolve b1e17 b1e1351
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1351
      have b1e1721 : (σ y) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b1e323
           have i₂ := b1e1624
           grind)
        | exact superpose b1e1624 b1e323
        | exact resolve b1e323 b1e1624
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e323
      have b1e1731 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e1721
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1721
        | exact resolve b1e1721 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1721
      have b1e1735 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e1731
           have i₂ := b1e1624
           grind)
        | exact superpose b1e1624 b1e1731
        | exact resolve b1e1731 b1e1624
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1624 b1e1731
      have b1e1736 : False := by grind
      exact b1e1736
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X0) := by
        intro X0 X1 X2
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
      have b2e34 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ x) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 X1 (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e46 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b2e49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
      have b2e52 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
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
      have b2e53 : (σ (M.op x y)) = (σ y) := by
        first
        | (have r₁ := b2e52
           have r₂ := b2e17
           grind)
        | exact resolve b2e52 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e52
      have b2e78 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e34 (σ y) (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e34
        | exact resolve b2e34 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34
      have b2e1076 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e78
           grind)
        | exact superpose b2e78 b2e16
        | exact resolve b2e16 b2e78
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e78
      have b2e1089 : (σ y) ≠ (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e1076
           have i₂ := b2e53
           grind)
        | exact superpose b2e53 b2e1076
        | exact resolve b2e1076 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e53 b2e1076
      have b2e1142 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e49 y y
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e49
        | exact resolve b2e49 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e49
      have b2e1282 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e11 (k y y)
           have i₂ := b2e1142
           grind)
        | exact superpose b2e1142 b2e11
        | exact resolve b2e11 b2e1142
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1142
      have b2e1295 : x = (k y y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e1282
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e1282
        | exact resolve b2e1282 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1282
      have b2e1302 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e46 y y
           have i₂ := b2e1295
           grind)
        | exact superpose b2e1295 b2e46
        | exact resolve b2e46 b2e1295
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46 b2e1295
      have b2e1305 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b2e1302
           have r₂ := b2e17
           grind)
        | exact resolve b2e1302 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1302
      have b2e1407 : x = (τ (σ y)) ∨ x = y := by
        first
        | (have i₁ := b2e11 x
           have i₂ := b2e1305
           grind)
        | exact superpose b2e1305 b2e11
        | exact resolve b2e11 b2e1305
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1305
      have b2e1423 : x = y ∨ x = y := by
        first
        | (have i₁ := b2e1407
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e1407
        | exact resolve b2e1407 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1407
      have b2e1424 : x = y := by grind
      clear b2e1423
      have b2e1512 : (σ y) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b2e1089
           have i₂ := b2e1424
           grind)
        | exact superpose b2e1424 b2e1089
        | exact resolve b2e1089 b2e1424
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1089
      have b2e1513 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e1512
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e1512
        | exact resolve b2e1512 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1512
      have b2e1515 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b2e1513
           have i₂ := b2e1424
           grind)
        | exact superpose b2e1424 b2e1513
        | exact resolve b2e1513 b2e1424
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1424 b2e1513
      have b2e1516 : False := by grind
      exact b2e1516
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
      have b3e35 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
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
      have b3e211 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b3e35 (σ x)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e35
      have b3e212 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e211
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e211
        | exact resolve b3e211 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e211
      have b3e213 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e212
           grind)
        | exact superpose b3e212 b3e16
        | exact resolve b3e16 b3e212
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e212
      have b3e274 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e213
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e213
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e213 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e213
      have b3e275 : x = (M.op y y) := by grind
      clear b3e274
      have b3e277 : False := by grind
      exact b3e277
