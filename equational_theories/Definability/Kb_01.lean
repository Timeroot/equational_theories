import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4402`: `x ◇ (x ◇ y) = (x ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation4402 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4402 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4402.models_iff G M).mp hM
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
      · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          grind
        have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b0e41 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b0e11 (σ x) X0 (σ x)
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e11
          | exact resolve b0e11 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e42 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b0e11 x X0 x
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e11
          | exact resolve b0e11 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e43 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b0e11 y X0 y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e11
          | exact resolve b0e11 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e47 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b0e42 x
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e42
          | exact resolve b0e42 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e42
        have b0e61 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X1 X2))) = X0 ∨ (k (M.op X1 X2) X0) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e11 X1 (M.op X1 X2) X2
             have i₂ := b0e15 (M.op X1 X2) X0
             grind)
          | (have i₁ := b0e11 X0 X1 X2
             have i₂ := b0e15 X0 (M.op (M.op X0 X2) X1)
             grind)
          | exact superpose b0e15 b0e11
          | (have j1 := b0e15 (M.op X1 X2) X0
             grind)
          | exact resolve b0e11 b0e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b0e156 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b0e41 (σ x)
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e41
          | exact resolve b0e41 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41
        have b0e1688 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e156
             grind)
          | exact superpose b0e156 b0e17
          | exact resolve b0e17 b0e156
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e156
        have b0e1723 : (M.op (σ y) (σ x)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b0e1688
             have i₂ := b0e47
             grind)
          | exact superpose b0e47 b0e1688
          | exact resolve b0e1688 b0e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e1688
        have b0e2381 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e63 x y
             grind)
          | exact superpose b0e63 b0e17
          | (have j1 := b0e63 x y
             grind)
          | exact resolve b0e17 b0e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e2444 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b0e63 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e63
        have b0e2458 : (σ (k y x)) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e2381
             have i₂ := b0e47
             grind)
          | exact superpose b0e47 b0e2381
          | exact resolve b0e2381 b0e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e2381
        have b0e2654 : ∀ X0 X1 : G, (M.op y (M.op y X1)) = X0 ∨ (M.op X0 (M.op y X1)) = (k (M.op y X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b0e43 (M.op y X1)
             have i₂ := b0e61 X0 y X1
             grind)
          | (have i₁ := b0e43 X0
             have i₂ := b0e61 (M.op y (M.op y X0)) X1 x
             grind)
          | exact superpose b0e61 b0e43
          | (have j1 := b0e61 X0 y X1
             grind)
          | exact resolve b0e43 b0e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e61
        have b0e2668 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (k (M.op y X1) X0) ∨ (M.op y X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b0e2654 X0 X1
             have i₂ := b0e43 X1
             grind)
          | exact superpose b0e43 b0e2654
          | (have j0 := b0e2654 X0 X1
             grind)
          | exact resolve b0e2654 b0e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e43 b0e2654
        have b0e11392 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e2444 y
             have i₂ := b0e23
             grind)
          | exact superpose b0e23 b0e2444
          | (have j0 := b0e2444 y
             grind)
          | exact resolve b0e2444 b0e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e23 b0e2444
        have b0e11398 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b0e11392
        have b0e14254 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b0e2668 X0 y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e2668
          | exact resolve b0e2668 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e2668
        have b0e36931 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b0e2458
             have i₂ := b0e14254 x
             grind)
          | exact superpose b0e14254 b0e2458
          | (have j1 := b0e14254 x
             grind)
          | exact resolve b0e2458 b0e14254
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e2458 b0e14254
        have b0e36959 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b0e36931
             have i₂ := b0e47
             grind)
          | exact superpose b0e47 b0e36931
          | exact resolve b0e36931 b0e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e47 b0e36931
        have b0e36960 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
        clear b0e36959
        have b0e36970 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b0e36960
             have i₂ := b0e11398
             grind)
          | exact superpose b0e11398 b0e36960
          | exact resolve b0e36960 b0e11398
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e36960
        have b0e36990 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b0e12 x
             have i₂ := b0e36970
             grind)
          | exact superpose b0e36970 b0e12
          | exact resolve b0e12 b0e36970
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e36970
        have b0e37027 : x = y ∨ x = y := by
          first
          | (have i₁ := b0e36990
             have i₂ := b0e12 y
             grind)
          | exact superpose b0e12 b0e36990
          | exact resolve b0e36990 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e36990
        have b0e37028 : x = y := by grind
        clear b0e37027
        have b0e38391 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b0e1723
             have i₂ := b0e37028
             grind)
          | exact superpose b0e37028 b0e1723
          | exact resolve b0e1723 b0e37028
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e1723 b0e37028
        have b0e38417 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e38391
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e38391
          | exact resolve b0e38391 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e38391
        have b0e38421 : False := by grind
        exact b0e38421
      · have b1e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X1) := by
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
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b1e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11 X0 X2 X3
             have i₂ := b1e11 X0 X2 X1
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11 X0 X3 (M.op X0 X2)
             have i₂ := b1e11 X0 X2 X1
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e11 (σ x) X0 (σ x)
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e11
          | exact resolve b1e11 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e11 x X0 x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e11
          | exact resolve b1e11 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 (M.op X0 (M.op X0 X1)))) := by
          intro X0 X1
          grind
        have b1e39 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b1e35 x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e35
          | exact resolve b1e35 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : ∀ X0 X1 : G, (M.op x (M.op x X1)) = (M.op (M.op y X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 x X1 (M.op x X0)
             have i₂ := b1e35 X0
             grind)
          | exact superpose b1e35 b1e11
          | exact resolve b1e11 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X1 : G, (M.op x (M.op x X1)) = (M.op y (M.op y X1)) := by
          intro X1
          first
          | (have i₁ := b1e41 x X1
             have i₂ := b1e11 y X1 x
             grind)
          | exact superpose b1e11 b1e41
          | exact resolve b1e41 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e43 : ∀ X1 : G, (M.op y X1) = (M.op y (M.op y X1)) := by
          intro X1
          first
          | (have i₁ := b1e42 X1
             have i₂ := b1e35 X1
             grind)
          | exact superpose b1e35 b1e42
          | exact resolve b1e42 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e49 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e55 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b1e71 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e26 X0 X1
             have i₂ := b1e15 X1 (τ X0)
             grind)
          | exact superpose b1e15 b1e26
          | (have j1 := b1e15 X1 (τ X0)
             grind)
          | exact resolve b1e26 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e196 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e49 (σ X1) (σ X0)
             have i₂ := b1e16 X0 X1
             grind)
          | exact superpose b1e16 b1e49
          | exact resolve b1e49 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e205 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e49 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e212 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ X2 ∨ (k X2 (M.op X0 X3)) = X2 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e205 X2 (M.op X0 X3)
             have i₂ := b1e30 X0 X3 X2 X1
             grind)
          | (have i₁ := b1e205 X2 (M.op X0 X3)
             have i₂ := b1e30 X0 X1 X2 X3
             grind)
          | exact superpose b1e30 b1e205
          | (have j0 := b1e205 X2 (M.op X0 X1)
             grind)
          | exact resolve b1e205 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e205
        have b1e270 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (σ x) X1)) = (M.op (M.op (M.op (σ y) X0) X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e32 (σ x) (M.op (σ x) X0) X2 X1
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e32
          | exact resolve b1e32 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e316 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) X1)) = (M.op (σ y) (M.op (σ y) X1)) := by
          intro X1
          first
          | (have i₁ := b1e270 x X1 x
             have i₂ := b1e32 (σ y) x x X1
             grind)
          | exact superpose b1e32 b1e270
          | exact resolve b1e270 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32 b1e270
        have b1e324 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ y) (M.op (σ y) X1)) := by
          intro X1
          first
          | (have i₁ := b1e316 X1
             have i₂ := b1e34 X1
             grind)
          | exact superpose b1e34 b1e316
          | exact resolve b1e316 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e316
        have b1e565 : ∀ X0 : G, (M.op (σ y) X0) = (k (M.op (σ y) X0) (M.op (σ x) (M.op (σ x) (M.op (σ y) X0)))) := by
          intro X0
          first
          | (have i₁ := b1e37 (σ x) (M.op (σ x) X0)
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e37
          | exact resolve b1e37 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e602 : ∀ X0 : G, (M.op (σ y) X0) = (k (M.op (σ y) X0) (M.op (σ y) (M.op (σ y) X0))) := by
          intro X0
          first
          | (have i₁ := b1e565 X0
             have i₂ := b1e34 (M.op (σ y) X0)
             grind)
          | exact superpose b1e34 b1e565
          | exact resolve b1e565 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e565
        have b1e613 : ∀ X0 : G, (M.op (σ y) X0) = (k (M.op (σ y) X0) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b1e602 X0
             have i₂ := b1e324 X0
             grind)
          | (have i₁ := b1e602 X0
             have i₂ := b1e324 (M.op (σ y) X0)
             grind)
          | exact superpose b1e324 b1e602
          | exact resolve b1e602 b1e324
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e324 b1e602
        have b1e2349 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e55 x x
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e55
          | exact resolve b1e55 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2370 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e17
             have i₂ := b1e55 x y
             grind)
          | exact superpose b1e55 b1e17
          | (have j1 := b1e55 x y
             grind)
          | exact resolve b1e17 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2433 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e55 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e2447 : (σ (k y x)) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e2370
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e2370
          | exact resolve b1e2370 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2370
        have b1e3883 : ∀ X0 X1 : G, (M.op y X0) ≠ X0 ∨ (k X0 (M.op x X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e212 x x X0 X1
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e212
          | (have j0 := b1e212 x X1 X0 X1
             grind)
          | exact resolve b1e212 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e212
        have b1e3994 : ∀ X0 X1 : G, (M.op y X0) ≠ (M.op y X0) ∨ (M.op y X0) = (k (M.op y X0) (M.op x X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e3883 (M.op y X0) X1
             have i₂ := b1e43 X0
             grind)
          | exact superpose b1e43 b1e3883
          | (have j0 := b1e3883 (M.op y X0) X1
             grind)
          | (have r₁ := b1e3883 (M.op y X1) X1
             have r₂ := b1e43 X1
             grind)
          | exact resolve b1e3883 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43 b1e3883
        have b1e4001 : ∀ X0 X1 : G, (M.op y X0) = (k (M.op y X0) (M.op x X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e3994 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3994
        have b1e4085 : ∀ X0 X1 : G, (M.op y X1) = (k (M.op y X1) (M.op y X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e4001 X1 (M.op x X0)
             have i₂ := b1e35 X0
             grind)
          | exact superpose b1e35 b1e4001
          | exact resolve b1e4001 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35 b1e4001
        have b1e11256 : ∀ X0 : G, (σ (M.op y X0)) ≠ (σ (M.op y X0)) ∨ (σ (M.op y X0)) = (M.op (σ (M.op y X0)) (σ (M.op y X0))) := by
          intro X0
          first
          | (have i₁ := b1e2433 (M.op y X0)
             have i₂ := b1e4085 X0 X0
             grind)
          | exact superpose b1e4085 b1e2433
          | (have j0 := b1e2433 (M.op y X0)
             grind)
          | exact resolve b1e2433 b1e4085
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2433 b1e4085
        have b1e11276 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ (M.op y X0)) (σ (M.op y X0))) := by
          intro X0
          first
          | (have j0 := b1e11256 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11256
        have b1e11351 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e71 (σ X0) X1
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e71
          | exact resolve b1e71 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71
        have b1e11552 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e11351 X0 X1
             have i₂ := b1e16 X1 X0
             grind)
          | exact superpose b1e16 b1e11351
          | (have j0 := b1e11351 X0 X1
             grind)
          | exact resolve b1e11351 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11351
        have b1e17691 : (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k x x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e196 x x
             grind)
          | exact superpose b1e196 b1e19
          | (have j1 := b1e196 x x
             grind)
          | exact resolve b1e19 b1e196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e196
        have b1e17838 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by grind
        clear b1e17691
        have b1e17841 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b1e17838
             have r₂ := b1e2349
             grind)
          | exact resolve b1e17838 b1e2349
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2349 b1e17838
        have b1e36041 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e2447
             have i₂ := b1e11552 x y
             grind)
          | exact superpose b1e11552 b1e2447
          | (have j1 := b1e11552 (σ x) (σ y)
             grind)
          | exact resolve b1e2447 b1e11552
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2447 b1e11552
        have b1e36042 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e36041
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e36041
          | exact resolve b1e36041 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e36041
        have b1e36043 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
        clear b1e36042
        have b1e38705 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e613 (σ y)
             have i₂ := b1e36043
             grind)
          | exact superpose b1e36043 b1e613
          | exact resolve b1e613 b1e36043
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e613 b1e36043
        have b1e38866 : (σ x) = (σ (k x x)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e38705
             have i₂ := b1e16 x x
             grind)
          | exact superpose b1e16 b1e38705
          | exact resolve b1e38705 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38705
        have b1e38905 : x = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e38866
             have i₂ := b1e17841
             grind)
          | exact superpose b1e17841 b1e38866
          | exact resolve b1e38866 b1e17841
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17841 b1e38866
        have b1e41634 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e11276 y
             have i₂ := b1e38905
             grind)
          | exact superpose b1e38905 b1e11276
          | exact resolve b1e11276 b1e38905
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11276 b1e38905
        have b1e41770 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e41634
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e41634
          | exact resolve b1e41634 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41634
        have b1e41771 : (σ x) = (σ y) := by grind
        clear b1e41770
        have b1e43218 : x = (τ (σ y)) := by
          first
          | (have i₁ := b1e12 x
             have i₂ := b1e41771
             grind)
          | exact superpose b1e41771 b1e12
          | exact resolve b1e12 b1e41771
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41771
        have b1e43253 : x = y := by
          first
          | (have i₁ := b1e43218
             have i₂ := b1e12 y
             grind)
          | exact superpose b1e12 b1e43218
          | exact resolve b1e43218 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43218
        have b1e44140 : y = (M.op y y) := by
          first
          | (have i₁ := b1e18
             have i₂ := b1e43253
             grind)
          | exact superpose b1e43253 b1e18
          | exact resolve b1e18 b1e43253
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43253
        have b1e44192 : False := by grind
        exact b1e44192
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b2e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          grind
        have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e18 : y = (M.op x x) := by grind
        have b2e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b2e22 : x = (k x y) := by grind
        have b2e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e11 X0 X2 X3
             have i₂ := b2e11 X0 X2 X1
             grind)
          | exact superpose b2e11 b2e11
          | exact resolve b2e11 b2e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
        have b2e268 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e57 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e269 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e268
             have i₂ := b2e16 x y
             grind)
          | exact superpose b2e16 b2e268
          | exact resolve b2e268 b2e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e268
        have b2e270 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e269
             have i₂ := b2e22
             grind)
          | exact superpose b2e22 b2e269
          | exact resolve b2e269 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22 b2e269
        have b2e273 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op (σ x) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e34 (σ y) (σ x) X0 X1
             have i₂ := b2e270
             grind)
          | exact superpose b2e270 b2e34
          | exact resolve b2e34 b2e270
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e275 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op (σ y) X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e11 (σ y) (σ x) X0
             have i₂ := b2e270
             grind)
          | exact superpose b2e270 b2e11
          | exact resolve b2e11 b2e270
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e276 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e275 X0
             have i₂ := b2e270
             grind)
          | exact superpose b2e270 b2e275
          | exact resolve b2e275 b2e270
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e270 b2e275
        have b2e278 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e276 x
             have i₂ := b2e273 (σ x) x
             grind)
          | exact superpose b2e273 b2e276
          | exact resolve b2e276 b2e273
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e273 b2e276
        have b2e417 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e278
             grind)
          | exact superpose b2e278 b2e19
          | exact resolve b2e19 b2e278
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e419 : (σ x) = (k (σ x) (σ x)) := by grind
        clear b2e278
        have b2e429 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b2e419
             have i₂ := b2e16 x x
             grind)
          | exact superpose b2e16 b2e419
          | exact resolve b2e419 b2e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e419
        have b2e576 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e429
             have i₂ := b2e15 x x
             grind)
          | exact superpose b2e15 b2e429
          | (have j1 := b2e15 x x
             grind)
          | exact resolve b2e429 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e429
        have b2e587 : (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e576
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e576
          | exact resolve b2e576 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e576
        have b2e589 : x = (M.op x x) := by
          first
          | (have r₁ := b2e587
             have r₂ := b2e417
             grind)
          | exact resolve b2e587 b2e417
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e587
        have b2e590 : x = y := by
          first
          | (have i₁ := b2e589
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e589
          | exact resolve b2e589 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e589
        have b2e754 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e417
             have i₂ := b2e590
             grind)
          | exact superpose b2e590 b2e417
          | exact resolve b2e417 b2e590
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e417 b2e590
        have b2e756 : False := by grind
        exact b2e756
      · have b3e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          grind
        have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e18 : y = (M.op x x) := by grind
        have b3e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b3e22 : x = (k x y) := by grind
        have b3e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e11 X0 X2 X3
             have i₂ := b3e11 X0 X2 X1
             grind)
          | exact superpose b3e11 b3e11
          | exact resolve b3e11 b3e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e48 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
        have b3e161 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e44 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e267 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b3e48 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e268 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e267
             have i₂ := b3e16 x y
             grind)
          | exact superpose b3e16 b3e267
          | exact resolve b3e267 b3e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e267
        have b3e269 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e268
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e268
          | exact resolve b3e268 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e22 b3e268
        have b3e270 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op (σ y) X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e11 (σ y) (σ x) X0
             have i₂ := b3e269
             grind)
          | exact superpose b3e269 b3e11
          | exact resolve b3e11 b3e269
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e273 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op (σ x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e27 (σ y) X0 X1 (σ x)
             have i₂ := b3e269
             grind)
          | exact superpose b3e269 b3e27
          | exact resolve b3e27 b3e269
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e278 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e270 x
             have i₂ := b3e273 x (σ x)
             grind)
          | exact superpose b3e273 b3e270
          | exact resolve b3e270 b3e273
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e270 b3e273
        have b3e279 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e278
             have i₂ := b3e269
             grind)
          | exact superpose b3e269 b3e278
          | exact resolve b3e278 b3e269
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e269 b3e278
        have b3e468 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e279
             grind)
          | exact superpose b3e279 b3e19
          | exact resolve b3e19 b3e279
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e480 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e161 (σ x) (σ x)
             have i₂ := b3e279
             grind)
          | exact superpose b3e279 b3e161
          | (have j0 := b3e161 (σ x) (σ x)
             grind)
          | (have r₁ := b3e161 (σ x) (σ x)
             have r₂ := b3e279
             grind)
          | exact resolve b3e161 b3e279
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e161 b3e279
        have b3e481 : (σ x) = (k (σ x) (σ x)) := by grind
        clear b3e480
        have b3e482 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e481
             have i₂ := b3e16 x x
             grind)
          | exact superpose b3e16 b3e481
          | exact resolve b3e481 b3e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e481
        have b3e721 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e482
             have i₂ := b3e15 x x
             grind)
          | exact superpose b3e15 b3e482
          | (have j1 := b3e15 x x
             grind)
          | exact resolve b3e482 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e482
        have b3e732 : (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e721
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e721
          | exact resolve b3e721 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e721
        have b3e734 : x = (M.op x x) := by
          first
          | (have r₁ := b3e732
             have r₂ := b3e468
             grind)
          | exact resolve b3e732 b3e468
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e732
        have b3e735 : x = y := by
          first
          | (have i₁ := b3e734
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e734
          | exact resolve b3e734 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e734
        have b3e894 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e468
             have i₂ := b3e735
             grind)
          | exact superpose b3e735 b3e468
          | exact resolve b3e468 b3e735
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e468 b3e735
        have b3e896 : False := by grind
        exact b3e896
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b4e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X1) := by
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
        have b4e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b4e41 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b4e11 y X0 y
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e11
          | exact resolve b4e11 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e58 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ y) = X0 := by
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
        have b4e60 : x = (M.op y x) ∨ y = (M.op x x) := by
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
        have b4e61 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b4e24
             have i₂ := b4e15 x y
             grind)
          | exact superpose b4e15 b4e24
          | (have j1 := b4e15 x y
             grind)
          | exact resolve b4e24 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e24
        have b4e65 : (σ x) = (σ (M.op y x)) := by
          first
          | (have r₁ := b4e61
             have r₂ := b4e18
             grind)
          | exact resolve b4e61 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e61
        have b4e66 : x = (M.op y x) := by
          first
          | (have r₁ := b4e60
             have r₂ := b4e18
             grind)
          | exact resolve b4e60 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e60
        have b4e69 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b4e11 y X0 x
             have i₂ := b4e66
             grind)
          | exact superpose b4e66 b4e11
          | exact resolve b4e11 b4e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e70 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b4e69 X0
             have i₂ := b4e41 X0
             grind)
          | exact superpose b4e41 b4e69
          | exact resolve b4e69 b4e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e41 b4e69
        have b4e72 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
          intro X0
          grind
        clear b4e25
        have b4e77 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b4e72 X0
             have i₂ := b4e13 X0
             grind)
          | exact superpose b4e13 b4e72
          | exact resolve b4e72 b4e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e72
        have b4e93 : y ≠ (M.op y x) := by
          first
          | (have i₁ := b4e18
             have i₂ := b4e70 x
             grind)
          | exact superpose b4e70 b4e18
          | exact resolve b4e18 b4e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e98 : x ≠ y := by
          first
          | (have i₁ := b4e93
             have i₂ := b4e66
             grind)
          | exact superpose b4e66 b4e93
          | exact resolve b4e93 b4e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e66 b4e93
        have b4e355 : (σ x) = (M.op (σ (M.op (τ (σ x)) (τ (σ x)))) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e77 (σ x)
             have i₂ := b4e58 (σ (M.op (τ (σ x)) (τ (σ x))))
             grind)
          | exact superpose b4e58 b4e77
          | (have j1 := b4e58 (σ (M.op (τ (σ x)) (τ (σ x))))
             grind)
          | exact resolve b4e77 b4e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e58 b4e77
        have b4e357 : (σ x) = (M.op (σ (M.op x x)) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e355
             have i₂ := b4e12 x
             grind)
          | exact superpose b4e12 b4e355
          | exact resolve b4e355 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e355
        have b4e360 : (σ x) = (M.op (σ (M.op y x)) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e357
             have i₂ := b4e70 x
             grind)
          | exact superpose b4e70 b4e357
          | exact resolve b4e357 b4e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e357
        have b4e362 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e360
             have i₂ := b4e65
             grind)
          | exact superpose b4e65 b4e360
          | exact resolve b4e360 b4e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e360
        have b4e364 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e362
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e362
          | exact resolve b4e362 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e362
        have b4e366 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b4e364
             have i₂ := b4e12 x
             grind)
          | exact superpose b4e12 b4e364
          | exact resolve b4e364 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e364
        have b4e368 : (σ y) = (σ (M.op y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b4e366
             have i₂ := b4e70 x
             grind)
          | exact superpose b4e70 b4e366
          | exact resolve b4e366 b4e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e70 b4e366
        have b4e370 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b4e368
             have i₂ := b4e65
             grind)
          | exact superpose b4e65 b4e368
          | exact resolve b4e368 b4e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e65 b4e368
        have b4e371 : (σ x) = (σ y) := by grind
        clear b4e370
        have b4e383 : x = (τ (σ y)) := by
          first
          | (have i₁ := b4e12 x
             have i₂ := b4e371
             grind)
          | exact superpose b4e371 b4e12
          | exact resolve b4e12 b4e371
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e371
        have b4e384 : x = y := by
          first
          | (have i₁ := b4e383
             have i₂ := b4e12 y
             grind)
          | exact superpose b4e12 b4e383
          | exact resolve b4e383 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e383
        have b4e390 : False := by grind
        exact b4e390
      · have b5e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          grind
        have b5e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b5e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b5e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b5e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b5e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b5e18 : y ≠ (M.op x x) := by grind
        have b5e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
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
        have b5e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b5e33 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
          intro X0
          grind
        clear b5e26
        have b5e37 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b5e33 X0
             have i₂ := b5e13 X0
             grind)
          | exact superpose b5e13 b5e33
          | exact resolve b5e33 b5e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e33
        have b5e66 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ y) = X0 := by
          intro X0
          first
          | (have i₁ := b5e19
             have i₂ := b5e15 (σ x) X0
             grind)
          | (have i₁ := b5e19
             have i₂ := b5e15 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b5e15 b5e19
          | (have j1 := b5e15 (σ x) X0
             grind)
          | exact resolve b5e19 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e70 : x = (M.op y x) ∨ y = (M.op x x) := by
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
        have b5e73 : x = (M.op y x) := by
          first
          | (have r₁ := b5e70
             have r₂ := b5e18
             grind)
          | exact resolve b5e70 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e70
        have b5e75 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b5e11 y X0 x
             have i₂ := b5e73
             grind)
          | exact superpose b5e73 b5e11
          | exact resolve b5e11 b5e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e136 : (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b5e75 x
             have i₂ := b5e73
             grind)
          | exact superpose b5e73 b5e75
          | exact resolve b5e75 b5e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e75
        have b5e144 : x = (M.op x x) := by
          first
          | (have i₁ := b5e136
             have i₂ := b5e73
             grind)
          | exact superpose b5e73 b5e136
          | exact resolve b5e136 b5e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e73 b5e136
        have b5e160 : x ≠ y := by
          first
          | (have i₁ := b5e18
             have i₂ := b5e144
             grind)
          | exact superpose b5e144 b5e18
          | exact resolve b5e18 b5e144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e536 : (σ x) = (M.op (σ (M.op (τ (σ x)) (τ (σ x)))) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b5e66 (σ (M.op (τ (σ x)) (τ (σ x))))
             have i₂ := b5e37 (σ x)
             grind)
          | exact superpose b5e37 b5e66
          | (have j0 := b5e66 (σ (M.op (τ (σ x)) (τ (σ x))))
             grind)
          | exact resolve b5e66 b5e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e37 b5e66
        have b5e539 : (σ x) = (M.op (σ (M.op x x)) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b5e536
             have i₂ := b5e12 x
             grind)
          | exact superpose b5e12 b5e536
          | exact resolve b5e536 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e536
        have b5e546 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b5e539
             have i₂ := b5e144
             grind)
          | exact superpose b5e144 b5e539
          | exact resolve b5e539 b5e144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e539
        have b5e549 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b5e546
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e546
          | exact resolve b5e546 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e546
        have b5e551 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e549
             have i₂ := b5e12 x
             grind)
          | exact superpose b5e12 b5e549
          | exact resolve b5e549 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e549
        have b5e553 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e551
             have i₂ := b5e144
             grind)
          | exact superpose b5e144 b5e551
          | exact resolve b5e551 b5e144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e144 b5e551
        have b5e554 : (σ x) = (σ y) := by grind
        clear b5e553
        have b5e661 : x = (τ (σ y)) := by
          first
          | (have i₁ := b5e12 x
             have i₂ := b5e554
             grind)
          | exact superpose b5e554 b5e12
          | exact resolve b5e12 b5e554
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e554
        have b5e662 : x = y := by
          first
          | (have i₁ := b5e661
             have i₂ := b5e12 y
             grind)
          | exact superpose b5e12 b5e661
          | exact resolve b5e661 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e661
        have b5e667 : False := by grind
        exact b5e667
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b6e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          grind
        have b6e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b6e29 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b6e11 y X0 y
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e11
          | exact resolve b6e11 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e45 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X1 X2))) = X0 ∨ (k (M.op X1 X2) X0) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e11 X1 (M.op X1 X2) X2
             have i₂ := b6e15 (M.op X1 X2) X0
             grind)
          | (have i₁ := b6e11 X0 X1 X2
             have i₂ := b6e15 X0 (M.op (M.op X0 X2) X1)
             grind)
          | exact superpose b6e15 b6e11
          | (have j1 := b6e15 (M.op X1 X2) X0
             grind)
          | exact resolve b6e11 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b6e2082 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e17
             have i₂ := b6e48 x y
             grind)
          | exact superpose b6e48 b6e17
          | (have j1 := b6e48 x y
             grind)
          | exact resolve b6e17 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2147 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e48 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48
        have b6e2353 : ∀ X0 X1 : G, (M.op y (M.op y X1)) = X0 ∨ (M.op X0 (M.op y X1)) = (k (M.op y X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e29 (M.op y X1)
             have i₂ := b6e45 X0 y X1
             grind)
          | (have i₁ := b6e29 X0
             have i₂ := b6e45 (M.op y (M.op y X0)) X1 x
             grind)
          | exact superpose b6e45 b6e29
          | (have j1 := b6e45 X0 y X1
             grind)
          | exact resolve b6e29 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45
        have b6e2367 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (k (M.op y X1) X0) ∨ (M.op y X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e2353 X0 X1
             have i₂ := b6e29 X1
             grind)
          | exact superpose b6e29 b6e2353
          | (have j0 := b6e2353 X0 X1
             grind)
          | exact resolve b6e2353 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29 b6e2353
        have b6e9993 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e2147 y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e2147
          | (have j0 := b6e2147 y
             grind)
          | exact resolve b6e2147 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e22 b6e2147
        have b6e9999 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b6e9993
        have b6e13520 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b6e2367 X0 y
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e2367
          | exact resolve b6e2367 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2367
        have b6e36101 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b6e2082
             have i₂ := b6e13520 x
             grind)
          | exact superpose b6e13520 b6e2082
          | (have j1 := b6e13520 x
             grind)
          | exact resolve b6e2082 b6e13520
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2082 b6e13520
        have b6e36118 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
        clear b6e36101
        have b6e36128 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b6e36118
             have i₂ := b6e9999
             grind)
          | exact superpose b6e9999 b6e36118
          | exact resolve b6e36118 b6e9999
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36118
        have b6e36135 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b6e12 x
             have i₂ := b6e36128
             grind)
          | exact superpose b6e36128 b6e12
          | exact resolve b6e12 b6e36128
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36128
        have b6e36173 : x = y ∨ x = y := by
          first
          | (have i₁ := b6e36135
             have i₂ := b6e12 y
             grind)
          | exact superpose b6e12 b6e36135
          | exact resolve b6e36135 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36135
        have b6e36174 : x = y := by grind
        clear b6e36173
        have b6e36278 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e36174
             grind)
          | exact superpose b6e36174 b6e19
          | exact resolve b6e19 b6e36174
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36174
        have b6e36305 : False := by grind
        exact b6e36305
      · have b7e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X1) := by
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
        have b7e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        clear b7e22
        have b7e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X1) = (M.op (M.op X0 X2) (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e11 (M.op X0 X2) X1 X3
             have i₂ := b7e11 X0 X1 X2
             grind)
          | exact superpose b7e11 b7e11
          | exact resolve b7e11 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e11 X0 X2 X3
             have i₂ := b7e11 X0 X2 X1
             grind)
          | exact superpose b7e11 b7e11
          | exact resolve b7e11 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e11 X0 X3 (M.op X0 X2)
             have i₂ := b7e11 X0 X2 X1
             grind)
          | exact superpose b7e11 b7e11
          | exact resolve b7e11 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op (M.op X0 X2) X3)) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e11 (M.op X0 X2) X3 X1
             have i₂ := b7e11 X0 X1 X2
             grind)
          | exact superpose b7e11 b7e11
          | exact resolve b7e11 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e38 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X0 X3)) = (M.op (M.op X0 X2) (M.op (M.op X0 X2) X3)) := by
          intro X0 X2 X3
          first
          | (have i₁ := b7e35 X0 x X2 X3
             have i₂ := b7e11 X0 X3 (M.op X0 x)
             grind)
          | exact superpose b7e11 b7e35
          | exact resolve b7e35 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e35
        have b7e44 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b7e50 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b7e54 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
        have b7e55 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
        have b7e56 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b7e58 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
        clear b7e28
        have b7e77 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op X0 X3) X4) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b7e32 X0 X3 X4 (M.op X0 X2)
             have i₂ := b7e11 X0 X2 X1
             grind)
          | exact superpose b7e11 b7e32
          | exact resolve b7e32 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e122 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b7e50 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e50
        have b7e130 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b7e44
        have b7e144 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b7e130 X0
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e130
          | exact resolve b7e130 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e130
        have b7e211 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ X1 ∨ (k X1 (M.op X0 X2)) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e122 X1 (M.op X0 X2)
             have i₂ := b7e11 X0 X1 X2
             grind)
          | exact superpose b7e11 b7e122
          | (have j0 := b7e122 X1 (M.op X0 X2)
             grind)
          | exact resolve b7e122 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e122
        have b7e213 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b7e54 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e54
        have b7e214 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b7e213
             have i₂ := b7e16 x y
             grind)
          | exact superpose b7e16 b7e213
          | exact resolve b7e213 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e213
        have b7e218 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op (σ (k x y)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b7e32 (σ y) X0 X1 (σ x)
             have i₂ := b7e214
             grind)
          | exact superpose b7e214 b7e32
          | exact resolve b7e32 b7e214
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e32
        have b7e361 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e144 X1
             have i₂ := b7e15 (σ X1) X0
             grind)
          | (have i₁ := b7e144 X0
             have i₂ := b7e15 X0 (M.op (σ X0) (σ X0))
             grind)
          | exact superpose b7e15 b7e144
          | (have j1 := b7e15 (σ X1) X0
             grind)
          | exact resolve b7e144 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e546 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X3)) = (M.op (M.op X0 X4) (M.op (M.op (M.op X0 X1) X2) X3)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b7e38 X0 X4 X3
             have i₂ := b7e77 X0 X1 X2 X4 X3
             grind)
          | exact superpose b7e77 b7e38
          | exact resolve b7e38 b7e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e77
        have b7e941 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op (σ (M.op y x)) X1) ∨ y = (M.op x x) := by
          intro X0 X1
          first
          | (have i₁ := b7e218 X0 X1
             have i₂ := b7e15 x y
             grind)
          | exact superpose b7e15 b7e218
          | (have j1 := b7e15 x y
             grind)
          | exact resolve b7e218 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e218
        have b7e1059 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op (σ (M.op y x)) X1) := by
          intro X0 X1
          first
          | (have j0 := b7e941 X0 X1
             grind)
          | (have r₁ := b7e941 X0 X1
             have r₂ := b7e18
             grind)
          | exact resolve b7e941 b7e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e941
        have b7e1277 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 X3)))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e11 X0 (M.op X0 (M.op X0 X3)) X1
             have i₂ := b7e31 X0 X3 X1 X2
             grind)
          | exact superpose b7e31 b7e11
          | exact resolve b7e11 b7e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e1282 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 X3)))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e38 X0 X1 (M.op X0 (M.op X0 X3))
             have i₂ := b7e31 X0 X3 X1 X2
             grind)
          | exact superpose b7e31 b7e38
          | exact resolve b7e38 b7e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e31 b7e38
        have b7e1316 : ∀ X0 X3 : G, (M.op X0 (M.op X0 X3)) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 X3)))) := by
          intro X0 X3
          first
          | (have i₁ := b7e1282 X0 x x X3
             have i₂ := b7e546 X0 x x X3 x
             grind)
          | exact superpose b7e546 b7e1282
          | exact resolve b7e1282 b7e546
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e546 b7e1282
        have b7e2431 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b7e56 X0 X0
             have i₂ := b7e15 (σ X0) X1
             grind)
          | (have i₁ := b7e56 X0 X1
             have i₂ := b7e15 X0 (M.op (σ X0) (σ X1))
             grind)
          | exact superpose b7e15 b7e56
          | (have j1 := b7e15 (σ X1) X0
             grind)
          | exact resolve b7e56 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e2452 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e56 x y
             grind)
          | exact superpose b7e56 b7e17
          | (have j1 := b7e56 x y
             grind)
          | exact resolve b7e17 b7e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e2495 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e144 X1
             have i₂ := b7e56 X0 X1
             grind)
          | exact superpose b7e56 b7e144
          | (have j1 := b7e56 X0 X1
             grind)
          | exact resolve b7e144 b7e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e2525 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b7e56 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e56
        have b7e2530 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e2495 X0 X1
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e2495
          | (have j0 := b7e2495 X0 X1
             grind)
          | exact resolve b7e2495 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2495
        have b7e8966 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b7e2525 (τ X0)
             have i₂ := b7e23 X0 (τ X0)
             grind)
          | exact superpose b7e23 b7e2525
          | (have j0 := b7e2525 (τ X0)
             grind)
          | exact resolve b7e2525 b7e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2525
        have b7e8968 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b7e8966 X0
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e8966
          | (have j0 := b7e8966 X0
             grind)
          | exact resolve b7e8966 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e8966
        have b7e8971 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b7e8968 X0
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e8968
          | (have j0 := b7e8968 X0
             grind)
          | exact resolve b7e8968 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e8968
        have b7e8984 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e55 (σ X0) X1
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e55
          | exact resolve b7e55 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e55
        have b7e9189 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b7e8984 X0 X1
             have i₂ := b7e16 X1 X0
             grind)
          | exact superpose b7e16 b7e8984
          | (have j0 := b7e8984 X0 X1
             grind)
          | exact resolve b7e8984 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e8984
        have b7e9217 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b7e8971 (τ X0)
             have i₂ := b7e58 X0 X0
             grind)
          | exact superpose b7e58 b7e8971
          | (have j0 := b7e8971 (τ X0)
             grind)
          | exact resolve b7e8971 b7e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e8971
        have b7e35033 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e2452
             have i₂ := b7e9189 x y
             grind)
          | exact superpose b7e9189 b7e2452
          | (have j1 := b7e9189 (σ x) (σ y)
             grind)
          | (have r₁ := b7e2452
             have r₂ := b7e9189 x y
             grind)
          | exact resolve b7e2452 b7e9189
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2452
        have b7e35034 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
        clear b7e35033
        have b7e35045 : y = (k y (τ (σ x))) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e144 y
             have i₂ := b7e35034
             grind)
          | exact superpose b7e35034 b7e144
          | exact resolve b7e144 b7e35034
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e144 b7e35034
        have b7e35197 : y = (k y x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e35045
             have i₂ := b7e12 x
             grind)
          | exact superpose b7e12 b7e35045
          | exact resolve b7e35045 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e35045
        have b7e35429 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e15 y x
             have i₂ := b7e35197
             grind)
          | exact superpose b7e35197 b7e15
          | (have j0 := b7e15 y x
             grind)
          | exact resolve b7e15 b7e35197
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e35197
        have b7e35434 : y = (M.op x y) ∨ x = (M.op y y) := by grind
        clear b7e35429
        have b7e36602 : ∀ X0 : G, y ≠ (M.op x y) ∨ y = (k y (M.op x X0)) ∨ x = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b7e211 x y X0
             have i₂ := b7e35434
             grind)
          | exact superpose b7e35434 b7e211
          | (have j0 := b7e211 x y X0
             grind)
          | exact resolve b7e211 b7e35434
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e211
        have b7e36665 : ∀ X0 : G, y = (k y (M.op x X0)) ∨ x = (M.op y y) := by
          intro X0
          first
          | (have j0 := b7e36602 X0
             grind)
          | (have r₁ := b7e36602 X0
             have r₂ := b7e35434
             grind)
          | exact resolve b7e36602 b7e35434
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e36602
        have b7e41613 : y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e36665 y
             have i₂ := b7e35434
             grind)
          | exact superpose b7e35434 b7e36665
          | exact resolve b7e36665 b7e35434
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e35434 b7e36665
        have b7e41655 : y = (k y y) ∨ x = (M.op y y) := by grind
        clear b7e41613
        have b7e43700 : y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e15 y y
             have i₂ := b7e41655
             grind)
          | exact superpose b7e41655 b7e15
          | (have j0 := b7e15 y y
             grind)
          | exact resolve b7e15 b7e41655
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e41655
        have b7e43704 : y = (M.op y y) ∨ x = (M.op y y) := by grind
        clear b7e43700
        have b7e43711 : x = (M.op y y) := by
          first
          | (have r₁ := b7e43704
             have r₂ := b7e20
             grind)
          | exact resolve b7e43704 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e43704
        have b7e45962 : x ≠ y := by
          first
          | (have i₁ := b7e20
             have i₂ := b7e43711
             grind)
          | exact superpose b7e43711 b7e20
          | exact resolve b7e20 b7e43711
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e45966 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b7e11 y X0 y
             have i₂ := b7e43711
             grind)
          | exact superpose b7e43711 b7e11
          | exact resolve b7e11 b7e43711
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e46038 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) X1) y) = (M.op y (M.op y (M.op y x))) := by
          intro X0 X1
          first
          | (have i₁ := b7e1277 y X0 X1 y
             have i₂ := b7e43711
             grind)
          | exact superpose b7e43711 b7e1277
          | exact resolve b7e1277 b7e43711
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1277
        have b7e46044 : (M.op y x) = (M.op y (M.op y (M.op y x))) := by
          first
          | (have i₁ := b7e1316 y y
             have i₂ := b7e43711
             grind)
          | exact superpose b7e43711 b7e1316
          | exact resolve b7e1316 b7e43711
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1316
        have b7e46054 : ∀ X0 X1 : G, (M.op y x) = (M.op (M.op (M.op y X0) X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b7e46038 X0 X1
             have i₂ := b7e46044
             grind)
          | exact superpose b7e46044 b7e46038
          | exact resolve b7e46038 b7e46044
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e46038 b7e46044
        have b7e46109 : (M.op y x) = (M.op y (M.op y y)) := by
          first
          | (have i₁ := b7e46054 x x
             have i₂ := b7e34 y x x y
             grind)
          | exact superpose b7e34 b7e46054
          | exact resolve b7e46054 b7e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e34 b7e46054
        have b7e46149 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b7e46109
             have i₂ := b7e45966 y
             grind)
          | exact superpose b7e45966 b7e46109
          | exact resolve b7e46109 b7e45966
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e45966 b7e46109
        have b7e85401 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e2431 X0 (τ X0)
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e2431
          | (have j0 := b7e2431 X1 (τ X0)
             grind)
          | exact resolve b7e2431 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2431
        have b7e85539 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e85401 X0 X1
             have i₂ := b7e23 X0 (τ X0)
             grind)
          | exact superpose b7e23 b7e85401
          | (have j0 := b7e85401 X0 X1
             grind)
          | exact resolve b7e85401 b7e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e23 b7e85401
        have b7e85550 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e85539 X0 X1
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e85539
          | (have j0 := b7e85539 X0 X1
             grind)
          | exact resolve b7e85539 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e85539
        have b7e225802 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (τ X0) = (k (τ X0) (τ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e361 X0 (τ X0)
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e361
          | (have j0 := b7e361 X1 (τ X0)
             grind)
          | exact resolve b7e361 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e361
        have b7e225820 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e225802 X0 X1
             have i₂ := b7e58 X1 X0
             grind)
          | exact superpose b7e58 b7e225802
          | (have j0 := b7e225802 X0 X1
             grind)
          | exact resolve b7e225802 b7e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e58 b7e225802
        have b7e234578 : (σ y) ≠ (σ (k x x)) ∨ x = (k x x) := by
          first
          | (have i₁ := b7e19
             have i₂ := b7e2530 x x
             grind)
          | exact superpose b7e2530 b7e19
          | (have j1 := b7e2530 x x
             grind)
          | exact resolve b7e19 b7e2530
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2530
        have b7e237314 : ∀ X0 : G, (σ X0) ≠ (σ y) ∨ x = X0 ∨ (k x X0) = (M.op X0 x) ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b7e234578
             have i₂ := b7e85550 x x
             grind)
          | (have i₁ := b7e234578
             have i₂ := b7e85550 X0 (k x x)
             grind)
          | exact superpose b7e85550 b7e234578
          | (have j1 := b7e85550 x X0
             grind)
          | (have r₁ := b7e234578
             have r₂ := b7e85550 (σ y) (σ (k x x))
             grind)
          | (have r₁ := b7e234578
             have r₂ := b7e85550 (σ (k x x)) (σ y)
             grind)
          | exact resolve b7e234578 b7e85550
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e85550 b7e234578
        have b7e237324 : ∀ X0 : G, (σ X0) ≠ (σ y) ∨ x = X0 ∨ (k x X0) = (M.op X0 x) := by
          intro X0
          first
          | (have j0 := b7e237314 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e237314
        have b7e257007 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b7e9217 X0
             have i₂ := b7e225820 X0 X0
             grind)
          | exact superpose b7e225820 b7e9217
          | (have j0 := b7e9217 X0
             have j1 := b7e225820 X0 X0
             grind)
          | (have r₁ := b7e9217 x
             have r₂ := b7e225820 x x
             grind)
          | exact resolve b7e9217 b7e225820
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e9217 b7e225820
        have b7e257010 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b7e257007 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e257007
        have b7e307846 : x = y ∨ (k x y) = (M.op y x) := by
          first
          | (have j0 := b7e237324 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e237324
        have b7e307847 : (k x y) = (M.op y x) := by
          first
          | (have r₁ := b7e307846
             have r₂ := b7e45962
             grind)
          | exact resolve b7e307846 b7e45962
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e45962 b7e307846
        have b7e313917 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b7e257010 (σ X0)
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e257010
          | (have j0 := b7e257010 (σ X0)
             grind)
          | exact resolve b7e257010 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e257010
        have b7e313959 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b7e313917 X0
             have i₂ := b7e16 X0 X0
             grind)
          | exact superpose b7e16 b7e313917
          | (have j0 := b7e313917 X0
             grind)
          | exact resolve b7e313917 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e313917
        have b7e318889 : ∀ X0 : G, (M.op (σ (M.op y x)) X0) = (M.op (σ (k y y)) X0) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b7e1059 (σ y) X0
             have i₂ := b7e313959 y
             grind)
          | exact superpose b7e313959 b7e1059
          | (have j1 := b7e313959 y
             grind)
          | exact resolve b7e1059 b7e313959
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e318920 : ∀ X0 : G, (M.op (σ (M.op y x)) X0) = (M.op (σ (k y y)) X0) := by
          intro X0
          first
          | (have j0 := b7e318889 X0
             grind)
          | (have r₁ := b7e318889 X0
             have r₂ := b7e20
             grind)
          | exact resolve b7e318889 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e318889
        have b7e327040 : ∀ X0 : G, (M.op (σ (M.op y x)) X0) = (M.op (σ (M.op y y)) X0) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b7e318920 X0
             have i₂ := b7e9189 y y
             grind)
          | exact superpose b7e9189 b7e318920
          | (have j1 := b7e9189 y y
             grind)
          | exact resolve b7e318920 b7e9189
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e318920
        have b7e327084 : ∀ X0 : G, (M.op (σ (M.op y x)) X0) = (M.op (σ (M.op y y)) X0) := by
          intro X0
          first
          | (have j0 := b7e327040 X0
             grind)
          | (have r₁ := b7e327040 X0
             have r₂ := b7e20
             grind)
          | exact resolve b7e327040 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e327040
        have b7e327105 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y x)) X0) := by
          intro X0
          first
          | (have i₁ := b7e327084 X0
             have i₂ := b7e43711
             grind)
          | exact superpose b7e43711 b7e327084
          | exact resolve b7e327084 b7e43711
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e327084
        have b7e329648 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op (σ x) X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e1059 X1 X0
             have i₂ := b7e327105 X0
             grind)
          | exact superpose b7e327105 b7e1059
          | exact resolve b7e1059 b7e327105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1059 b7e327105
        have b7e332285 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b7e11 (σ y) X0 x
             have i₂ := b7e329648 X0 x
             grind)
          | exact superpose b7e329648 b7e11
          | exact resolve b7e11 b7e329648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e329648
        have b7e343676 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (k y y))) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b7e332285 (σ y)
             have i₂ := b7e313959 y
             grind)
          | exact superpose b7e313959 b7e332285
          | (have j1 := b7e313959 y
             grind)
          | exact resolve b7e332285 b7e313959
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e313959 b7e332285
        have b7e343976 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (k y y))) := by
          first
          | (have r₁ := b7e343676
             have r₂ := b7e20
             grind)
          | exact resolve b7e343676 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e343676
        have b7e356545 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y y))) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b7e343976
             have i₂ := b7e9189 y y
             grind)
          | exact superpose b7e9189 b7e343976
          | (have j1 := b7e9189 y y
             grind)
          | exact resolve b7e343976 b7e9189
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e9189 b7e343976
        have b7e356655 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y y))) := by
          first
          | (have r₁ := b7e356545
             have r₂ := b7e20
             grind)
          | exact resolve b7e356545 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e356545
        have b7e356713 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b7e356655
             have i₂ := b7e43711
             grind)
          | exact superpose b7e43711 b7e356655
          | exact resolve b7e356655 b7e43711
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e43711 b7e356655
        have b7e356754 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b7e356713
             have i₂ := b7e214
             grind)
          | exact superpose b7e214 b7e356713
          | exact resolve b7e356713 b7e214
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e214 b7e356713
        have b7e356778 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b7e356754
             have i₂ := b7e307847
             grind)
          | exact superpose b7e307847 b7e356754
          | exact resolve b7e356754 b7e307847
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e307847 b7e356754
        have b7e358171 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e356778
             grind)
          | exact superpose b7e356778 b7e17
          | exact resolve b7e17 b7e356778
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e356778
        have b7e358333 : (σ (M.op y x)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b7e358171
             have i₂ := b7e46149
             grind)
          | exact superpose b7e46149 b7e358171
          | exact resolve b7e358171 b7e46149
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e46149 b7e358171
        have b7e358334 : False := by grind
        exact b7e358334

/-- `Equation4411`: `x ◇ (x ◇ y) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4411 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4411 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4411.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
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
      have b0e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X2 X0 X3
           have i₂ := b0e10 X2 X0 X1
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (M.op (σ y) X0) := by
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
      have b0e38 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op y X0) := by
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
      have b0e41 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e38 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e38
        | exact resolve b0e38 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 x X1
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e10
        | exact resolve b0e10 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X1 X0 (M.op X0 x)
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e10
        | exact resolve b0e10 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e52 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X2)) ∨ (M.op X2 X0) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 X2 X2
           have i₂ := b0e14 X2 X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op X1 X2)
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X2 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e53 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X2) X1) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 X1 X2
           have i₂ := b0e14 X1 X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op X0 X1)
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X1 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
      have b0e62 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
      have b0e115 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op X2 X3) X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e34 X2 X3 X4 (M.op X2 X0)
           have i₂ := b0e10 X2 X0 X1
           grind)
        | exact superpose b0e10 b0e34
        | exact resolve b0e34 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e116 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e34 X0 X1 X2 (M.op X0 x)
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e34
        | exact resolve b0e34 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e117 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 X2) X3) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e34 X1 X2 X3 X1
           have i₂ := b0e14 X1 X0
           grind)
        | (have i₁ := b0e34 X0 X1 X2 X3
           have i₂ := b0e14 X0 (M.op X0 X3)
           grind)
        | exact superpose b0e14 b0e34
        | (have j1 := b0e14 X1 X0
           grind)
        | exact resolve b0e34 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e124 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op x y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e34 y X0 X1 x
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e34
        | exact resolve b0e34 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e157 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e124 X0 X1
           have i₂ := b0e43 X1 y
           grind)
        | exact superpose b0e43 b0e124
        | exact resolve b0e124 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e124
      have b0e159 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op (M.op y (M.op X0 X1)) X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e115 X0 X1 X2 X3 X4
           have i₂ := b0e116 (M.op X0 X1) X2 X4
           grind)
        | exact superpose b0e116 b0e115
        | exact resolve b0e115 b0e116
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e115
      have b0e169 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op (M.op y y) X4) := by
        intro X2 X3 X4
        first
        | (have i₁ := b0e159 x x X2 X3 X4
           have i₂ := b0e116 y (M.op x x) X4
           grind)
        | (have i₁ := b0e159 x x X2 X3 X2
           have i₂ := b0e116 (M.op x x) x X2
           grind)
        | exact superpose b0e116 b0e159
        | exact resolve b0e159 b0e116
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e159
      have b0e172 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op y X4) := by
        intro X2 X3 X4
        first
        | (have i₁ := b0e169 X2 X3 X4
           have i₂ := b0e157 y X4
           grind)
        | exact superpose b0e157 b0e169
        | exact resolve b0e169 b0e157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e157 b0e169
      have b0e182 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e172 (σ x) (σ x) X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e172
        | exact resolve b0e172 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e192 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 x
           have i₂ := b0e172 X1 x X0
           grind)
        | exact superpose b0e172 b0e10
        | exact resolve b0e10 b0e172
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e201 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op y x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e38 (M.op X0 X1)
           have i₂ := b0e172 X0 X1 x
           grind)
        | exact superpose b0e172 b0e38
        | exact resolve b0e38 b0e172
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e202 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y (M.op y x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e201 X0 X1
           have i₂ := b0e172 X0 X1 (M.op y x)
           grind)
        | exact superpose b0e172 b0e201
        | exact resolve b0e201 b0e172
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e201
      have b0e213 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y y) := by
        intro X0 X1
        first
        | (have i₁ := b0e202 X0 X1
           have i₂ := b0e38 y
           grind)
        | exact superpose b0e38 b0e202
        | exact resolve b0e202 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e202
      have b0e232 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
      have b0e261 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
        first
        | (have i₁ := b0e232
           have i₂ := b0e182 (σ x)
           grind)
        | exact superpose b0e182 b0e232
        | exact resolve b0e232 b0e182
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e232
      have b0e336 : (M.op y (σ y)) = (M.op (σ y) (M.op y x)) := by
        first
        | (have i₁ := b0e38 (σ y)
           have i₂ := b0e182 x
           grind)
        | exact superpose b0e182 b0e38
        | exact resolve b0e38 b0e182
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e337 : (M.op y (M.op y x)) = (M.op y (σ y)) := by
        first
        | (have i₁ := b0e336
           have i₂ := b0e182 (M.op y x)
           grind)
        | exact superpose b0e182 b0e336
        | exact resolve b0e336 b0e182
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e336
      have b0e351 : (M.op y y) = (M.op y (σ y)) := by
        first
        | (have i₁ := b0e337
           have i₂ := b0e38 y
           grind)
        | exact superpose b0e38 b0e337
        | exact resolve b0e337 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e337
      have b0e373 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e51 (σ X1) (σ X0)
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e51
        | exact resolve b0e51 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e379 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e51 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51
      have b0e2513 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (M.op (σ X0) X2) (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X0 X1
           have i₂ := b0e53 (σ X1) (σ X0) X2
           grind)
        | exact superpose b0e53 b0e15
        | (have j1 := b0e53 (σ X1) (σ X0) X2
           grind)
        | exact resolve b0e15 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53
      have b0e2516 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (M.op y (σ X0)) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e2513 X0 X1 x
           have i₂ := b0e116 (σ X0) x (σ X0)
           grind)
        | exact superpose b0e116 b0e2513
        | (have j0 := b0e2513 X0 X1 x
           grind)
        | exact resolve b0e2513 b0e116
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e116 b0e2513
      have b0e2618 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (M.op (σ X0) y)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e2516 X0 X1
           have i₂ := b0e10 (σ X0) y (σ X0)
           grind)
        | exact superpose b0e10 b0e2516
        | (have j0 := b0e2516 X0 X1
           grind)
        | exact resolve b0e2516 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2516
      have b0e2693 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (M.op y y) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e2618 X0 X1
           have i₂ := b0e44 y (σ X0)
           grind)
        | exact superpose b0e44 b0e2618
        | (have j0 := b0e2618 X0 X1
           grind)
        | exact resolve b0e2618 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44 b0e2618
      have b0e2734 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op y (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e2693 X0 X1
           have i₂ := b0e172 y y (σ X0)
           grind)
        | exact superpose b0e172 b0e2693
        | (have j0 := b0e2693 X0 X1
           grind)
        | exact resolve b0e2693 b0e172
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2693
      have b0e4031 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e29 X1 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e29
        | exact resolve b0e29 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e4116 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e55 X0 X0
           have i₂ := b0e14 (σ X0) X1
           grind)
        | (have i₁ := b0e55 X0 X1
           have i₂ := b0e14 X0 (M.op (σ X0) (σ X1))
           grind)
        | exact superpose b0e14 b0e55
        | (have j1 := b0e14 (σ X1) X0
           grind)
        | exact resolve b0e55 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e4159 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1
           have i₂ := b0e55 X0 X1
           grind)
        | exact superpose b0e55 b0e11
        | (have j1 := b0e55 X0 X1
           grind)
        | exact resolve b0e11 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e4168 : ∀ X0 : G, (σ X0) = (M.op y (σ y)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e182 (σ y)
           have i₂ := b0e55 y X0
           grind)
        | exact superpose b0e55 b0e182
        | (have j1 := b0e55 y X0
           grind)
        | exact resolve b0e182 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e4206 : ∀ X0 : G, (σ X0) = (M.op y y) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e4168 X0
           have i₂ := b0e351
           grind)
        | exact superpose b0e351 b0e4168
        | (have j0 := b0e4168 X0
           grind)
        | exact resolve b0e4168 b0e351
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e351 b0e4168
      have b0e4249 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (σ X0) = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b0e4206 X0
           have i₂ := b0e182 (σ X0)
           grind)
        | exact superpose b0e182 b0e4206
        | (have j0 := b0e4206 X0
           grind)
        | exact resolve b0e4206 b0e182
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e182 b0e4206
      have b0e4322 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      have b0e4342 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e4322 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e4322
        | exact resolve b0e4322 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4322
      have b0e4351 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e261
           grind)
        | exact superpose b0e261 b0e16
        | exact resolve b0e16 b0e261
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e261
      have b0e4410 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op y X0) ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e379 (M.op X1 X2) X0
           have i₂ := b0e172 X1 X2 X0
           grind)
        | exact superpose b0e172 b0e379
        | (have j0 := b0e379 (M.op X1 X2) X0
           grind)
        | (have r₁ := b0e379 (M.op y x) x
           have r₂ := b0e172 y x x
           grind)
        | exact resolve b0e379 b0e172
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e12385 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e62 X0 (σ X0)
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e62
        | exact resolve b0e62 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62
      have b0e12535 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e12385 X0 X1
           have i₂ := b0e15 X1 X0
           grind)
        | exact superpose b0e15 b0e12385
        | (have j0 := b0e12385 X0 X1
           grind)
        | exact resolve b0e12385 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12385
      have b0e13003 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op X4 X2) ∨ (M.op X3 X4) = (k X3 X4) ∨ (M.op X0 X2) = (k X0 X2) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e52 X4 X2 X3
           have i₂ := b0e117 X2 X0 X1 (M.op X2 X3)
           grind)
        | (have i₁ := b0e52 X0 (M.op X1 X2) X2
           have i₂ := b0e117 X0 X1 X2 (M.op (M.op X1 X2) X2)
           grind)
        | exact superpose b0e117 b0e52
        | (have j0 := b0e52 X4 X1 X3
           have j1 := b0e117 X4 X3 X2 X3
           grind)
        | exact resolve b0e52 b0e117
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52 b0e117
      have b0e13302 : ∀ X0 X2 X3 X4 : G, (M.op y (M.op X2 X3)) = (M.op X4 X2) ∨ (M.op X3 X4) = (k X3 X4) ∨ (M.op X0 X2) = (k X0 X2) := by
        intro X0 X2 X3 X4
        first
        | (have i₁ := b0e13003 X0 x X2 X3 X4
           have i₂ := b0e172 X0 x (M.op X2 X3)
           grind)
        | exact superpose b0e172 b0e13003
        | (have j0 := b0e13003 X3 x X4 X3 X4
           grind)
        | exact resolve b0e13003 b0e172
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13003
      have b0e13562 : ∀ X0 X2 X3 X4 : G, (M.op y y) = (M.op X4 X2) ∨ (M.op X3 X4) = (k X3 X4) ∨ (M.op X0 X2) = (k X0 X2) := by
        intro X0 X2 X3 X4
        first
        | (have i₁ := b0e13302 X0 X2 X3 X4
           have i₂ := b0e213 X2 X3
           grind)
        | exact superpose b0e213 b0e13302
        | (have j0 := b0e13302 X3 X4 X3 X4
           grind)
        | exact resolve b0e13302 b0e213
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13302
      have b0e23412 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e373 x x
           grind)
        | exact superpose b0e373 b0e18
        | (have j1 := b0e373 x x
           grind)
        | exact resolve b0e18 b0e373
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e373
      have b0e27150 : ∀ X0 : G, (τ (σ y)) = X0 ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e4159 x X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e4159
        | (have j0 := b0e4159 x X0
           grind)
        | exact resolve b0e4159 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e27201 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) := by
        first
        | (have i₁ := b0e4159 x x
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e4159
        | exact resolve b0e4159 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4159
      have b0e27333 : (σ y) = (σ (k x x)) ∨ x = y := by
        first
        | (have i₁ := b0e27201
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e27201
        | exact resolve b0e27201 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27201
      have b0e27347 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e27150 X0
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e27150
        | (have j0 := b0e27150 X0
           grind)
        | exact resolve b0e27150 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27150
      have b0e27478 : ∀ X0 : G, (k (k x x) (τ X0)) = (τ (k (σ y) X0)) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b0e67 (k x x) X0
           have i₂ := b0e27333
           grind)
        | exact superpose b0e27333 b0e67
        | exact resolve b0e67 b0e27333
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27333
      have b0e27495 : ∀ X0 : G, (k y (τ X0)) = (k (k x x) (τ X0)) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b0e27478 X0
           have i₂ := b0e67 y X0
           grind)
        | exact superpose b0e67 b0e27478
        | exact resolve b0e27478 b0e67
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67 b0e27478
      have b0e27670 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e4116 X0 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e4116
        | (have j0 := b0e4116 X1 (τ X0)
           grind)
        | exact resolve b0e4116 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4116
      have b0e27817 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e27670 X0 X1
           have i₂ := b0e24 X0 (τ X0)
           grind)
        | exact superpose b0e24 b0e27670
        | (have j0 := b0e27670 X0 X1
           grind)
        | exact resolve b0e27670 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27670
      have b0e27835 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e27817 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e27817
        | (have j0 := b0e27817 X0 X1
           grind)
        | exact resolve b0e27817 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27817
      have b0e27859 : ∀ X0 : G, (M.op (σ x) X0) = (σ (k x (τ X0))) ∨ (τ X0) = y := by
        intro X0
        first
        | (have i₁ := b0e27347 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e27347
        | (have j0 := b0e27347 (τ X0)
           grind)
        | exact resolve b0e27347 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e27879 : x = (k x (τ (σ (k x x)))) ∨ x = y := by
        first
        | (have i₁ := b0e4342 x
           have i₂ := b0e27347 x
           grind)
        | exact superpose b0e27347 b0e4342
        | (have j1 := b0e27347 x
           grind)
        | exact resolve b0e4342 b0e27347
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4342
      have b0e27922 : ∀ X0 X1 : G, (M.op y X1) = (M.op (σ (k x X0)) X1) ∨ y = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e172 (σ x) (σ X0) X1
           have i₂ := b0e27347 X0
           grind)
        | exact superpose b0e27347 b0e172
        | (have j1 := b0e27347 X0
           grind)
        | exact resolve b0e172 b0e27347
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e172 b0e27347
      have b0e27969 : x = (k x (k x x)) ∨ x = y := by
        first
        | (have i₁ := b0e27879
           have i₂ := b0e11 (k x x)
           grind)
        | exact superpose b0e11 b0e27879
        | exact resolve b0e27879 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27879
      have b0e27974 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ (τ X0) = y := by
        intro X0
        first
        | (have i₁ := b0e27859 X0
           have i₂ := b0e24 X0 x
           grind)
        | exact superpose b0e24 b0e27859
        | (have j0 := b0e27859 X0
           grind)
        | exact resolve b0e27859 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24 b0e27859
      have b0e30187 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op y (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op y (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e2734 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2734
      have b0e33845 : ∀ X0 : G, (k (τ (σ x)) X0) = (τ (M.op (σ x) (σ X0))) ∨ (τ (σ X0)) = y := by
        intro X0
        first
        | (have i₁ := b0e29 (σ x) X0
           have i₂ := b0e27974 (σ X0)
           grind)
        | exact superpose b0e27974 b0e29
        | (have j1 := b0e27974 (σ X0)
           grind)
        | exact resolve b0e29 b0e27974
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29 b0e27974
      have b0e33861 : ∀ X0 : G, (k x X0) = (τ (M.op (σ x) (σ X0))) ∨ (τ (σ X0)) = y := by
        intro X0
        first
        | (have i₁ := b0e33845 X0
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e33845
        | (have j0 := b0e33845 X0
           grind)
        | exact resolve b0e33845 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33845
      have b0e33887 : ∀ X0 : G, (k x X0) = (τ (M.op (σ x) (σ X0))) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e33861 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e33861
        | (have j0 := b0e33861 X0
           grind)
        | exact resolve b0e33861 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33861
      have b0e39843 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ (k x x)) := by
        first
        | (have i₁ := b0e11 (k x x)
           have i₂ := b0e23412
           grind)
        | exact superpose b0e23412 b0e11
        | exact resolve b0e11 b0e23412
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23412
      have b0e39904 : (σ x) = (σ (k x x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e39843
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e39843
        | exact resolve b0e39843 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39843
      have b0e40351 : (τ (M.op (σ x) (σ x))) = (k x (k x x)) ∨ y = (k x x) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e33887 (k x x)
           have i₂ := b0e39904
           grind)
        | exact superpose b0e39904 b0e33887
        | (have j0 := b0e33887 (k x x)
           grind)
        | exact resolve b0e33887 b0e39904
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33887 b0e39904
      have b0e40352 : (τ (M.op (σ x) (σ x))) = (k x (k x x)) ∨ y = (k x x) := by grind
      clear b0e40351
      have b0e40357 : (τ (σ y)) = (k x (k x x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e40352
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e40352
        | exact resolve b0e40352 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40352
      have b0e40384 : y = (k x (k x x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e40357
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e40357
        | exact resolve b0e40357 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40357
      have b0e41505 : y = (M.op x (k x x)) ∨ (M.op x x) = (k x x) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e14 x (k x x)
           have i₂ := b0e40384
           grind)
        | exact superpose b0e40384 b0e14
        | (have j0 := b0e14 x (k x x)
           grind)
        | exact resolve b0e14 b0e40384
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41525 : (σ y) = (σ (M.op x (k x x))) ∨ (M.op x x) = (k x x) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e12535 (k x x) x
           have i₂ := b0e40384
           grind)
        | exact superpose b0e40384 b0e12535
        | (have j0 := b0e12535 (k x x) x
           grind)
        | exact resolve b0e12535 b0e40384
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12535
      have b0e41534 : y = (k x x) ∨ (σ y) = (σ (M.op x (k x x))) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e41525
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e41525
        | exact resolve b0e41525 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41525
      have b0e41535 : (σ y) = (σ (M.op x (k x x))) ∨ y = (k x x) := by grind
      clear b0e41534
      have b0e41544 : y = (k x x) ∨ y = (M.op x (k x x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e41505
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e41505
        | exact resolve b0e41505 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41505
      have b0e41545 : y = (M.op x (k x x)) ∨ y = (k x x) := by grind
      clear b0e41544
      have b0e41857 : x ≠ y ∨ x = (k x (k x x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e379 x (k x x)
           have i₂ := b0e41545
           grind)
        | exact superpose b0e41545 b0e379
        | (have j0 := b0e379 x (k x x)
           grind)
        | exact resolve b0e379 b0e41545
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e379 b0e41545
      have b0e41870 : x = (k x (k x x)) ∨ y = (k x x) := by
        first
        | (have r₁ := b0e41857
           have r₂ := b0e27969
           grind)
        | exact resolve b0e41857 b0e27969
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27969 b0e41857
      have b0e42512 : ∀ X0 : G, (M.op (σ x) X0) = (M.op y X0) ∨ y = (k x x) ∨ y = (k x x) := by
        intro X0
        first
        | (have i₁ := b0e27922 (k x x) X0
           have i₂ := b0e41870
           grind)
        | exact superpose b0e41870 b0e27922
        | (have j0 := b0e27922 (k x x) x
           grind)
        | exact resolve b0e27922 b0e41870
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27922
      have b0e42515 : x = (M.op x (k x x)) ∨ (M.op x x) = (k x x) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e14 x (k x x)
           have i₂ := b0e41870
           grind)
        | exact superpose b0e41870 b0e14
        | (have j0 := b0e14 x (k x x)
           grind)
        | exact resolve b0e14 b0e41870
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41870
      have b0e42536 : ∀ X0 : G, (M.op (σ x) X0) = (M.op y X0) ∨ y = (k x x) := by
        intro X0
        first
        | (have j0 := b0e42512 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42512
      have b0e42549 : y = (k x x) ∨ x = (M.op x (k x x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e42515
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e42515
        | exact resolve b0e42515 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42515
      have b0e42550 : x = (M.op x (k x x)) ∨ y = (k x x) := by grind
      clear b0e42549
      have b0e44217 : (M.op x x) = (M.op y x) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e192 x (k x x)
           have i₂ := b0e42550
           grind)
        | exact superpose b0e42550 b0e192
        | exact resolve b0e192 b0e42550
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e192 b0e42550
      have b0e44238 : (M.op x y) = (M.op x x) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e44217
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e44217
        | exact resolve b0e44217 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44217
      have b0e44273 : y = (k x x) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e44238
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e44238
        | exact resolve b0e44238 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44238
      have b0e49142 : (σ y) = (M.op y (σ x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e42536 (σ x)
           grind)
        | exact superpose b0e42536 b0e18
        | exact resolve b0e18 b0e42536
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42536
      have b0e78209 : ∀ X0 : G, (k y X0) = (k (k x x) X0) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b0e27495 (σ X0)
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e27495
        | exact resolve b0e27495 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27495
      have b0e81515 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e27835 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27835
      have b0e86444 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) X0) := by
        intro X0
        first
        | (have j0 := b0e4410 X0 y X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4410
      have b0e86464 : ∀ X0 X1 : G, (M.op y y) = (k (M.op y y) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e86444 (M.op X0 X1)
           have i₂ := b0e213 X0 X1
           grind)
        | exact superpose b0e213 b0e86444
        | exact resolve b0e86444 b0e213
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e213 b0e86444
      have b0e130354 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op y (σ (τ X0))) ∨ (M.op y (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e30187 (τ X0) (τ X1)
           have i₂ := b0e4031 X1 X0
           grind)
        | exact superpose b0e4031 b0e30187
        | (have j0 := b0e30187 (τ X0) (τ X1)
           grind)
        | exact resolve b0e30187 b0e4031
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4031 b0e30187
      have b0e130409 : ∀ X0 X1 : G, (M.op y X0) ≠ (σ (τ (k X0 X1))) ∨ (M.op y (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e130354 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e130354
        | (have j0 := b0e130354 X0 X1
           grind)
        | exact resolve b0e130354 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e130354
      have b0e130419 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op y X0) ∨ (M.op y (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e130409 X0 X1
           have i₂ := b0e12 (k X0 X1)
           grind)
        | exact superpose b0e12 b0e130409
        | (have j0 := b0e130409 X0 X1
           grind)
        | exact resolve b0e130409 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e130409
      have b0e130426 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (M.op y (σ (τ X0))) ∨ (k X0 X1) ≠ (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e130419 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e130419
        | (have j0 := b0e130419 X0 X1
           grind)
        | exact resolve b0e130419 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e130419
      have b0e130430 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op y X0) ∨ (M.op X0 X1) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e130426 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e130426
        | (have j0 := b0e130426 X0 X1
           grind)
        | exact resolve b0e130426 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e130426
      have b0e137074 : y ≠ (M.op y x) ∨ (M.op y x) = (M.op x (k x x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e130430 x (k x x)
           have i₂ := b0e40384
           grind)
        | exact superpose b0e40384 b0e130430
        | (have j0 := b0e130430 x (k x x)
           grind)
        | exact resolve b0e130430 b0e40384
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40384 b0e130430
      have b0e137110 : y ≠ (M.op x y) ∨ (M.op y x) = (M.op x (k x x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e137074
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e137074
        | exact resolve b0e137074 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e137074
      have b0e137142 : (M.op y x) = (M.op x (k x x)) ∨ y = (k x x) := by
        first
        | (have r₁ := b0e137110
           have r₂ := b0e44273
           grind)
        | exact resolve b0e137110 b0e44273
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44273 b0e137110
      have b0e137171 : (M.op x y) = (M.op x (k x x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e137142
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e137142
        | exact resolve b0e137142 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e137142
      have b0e140482 : (σ (M.op x y)) = (σ y) ∨ y = (k x x) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e41535
           have i₂ := b0e137171
           grind)
        | exact superpose b0e137171 b0e41535
        | exact resolve b0e41535 b0e137171
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41535 b0e137171
      have b0e140549 : (σ (M.op x y)) = (σ y) ∨ y = (k x x) := by grind
      clear b0e140482
      have b0e140995 : (σ y) ≠ (M.op y (σ x)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e4351
           have i₂ := b0e140549
           grind)
        | exact superpose b0e140549 b0e4351
        | exact resolve b0e4351 b0e140549
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e140549
      have b0e141060 : y = (k x x) := by
        first
        | (have r₁ := b0e140995
           have r₂ := b0e49142
           grind)
        | exact resolve b0e140995 b0e49142
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49142 b0e140995
      have b0e144022 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (M.op y y) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e13562 X0 X1 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13562
      have b0e144023 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op y y) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e144022 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e144022
      have b0e144284 : ∀ X0 X1 : G, y = (k y (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        grind
      clear b0e144023
      have b0e144666 : ∀ X0 : G, y = (k y y) ∨ (M.op X0 x) = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b0e144284 x X0
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e144284
        | (have j0 := b0e144284 x X0
           grind)
        | exact resolve b0e144284 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e144284
      have b0e144924 : (k y x) = (M.op (k x x) x) ∨ x = y ∨ y = (k y y) := by
        first
        | (have i₁ := b0e78209 x
           have i₂ := b0e144666 (k x x)
           grind)
        | exact superpose b0e144666 b0e78209
        | exact resolve b0e78209 b0e144666
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78209 b0e144666
      have b0e144941 : (M.op y x) = (k y x) ∨ x = y ∨ y = (k y y) := by
        first
        | (have i₁ := b0e144924
           have i₂ := b0e141060
           grind)
        | exact superpose b0e141060 b0e144924
        | exact resolve b0e144924 b0e141060
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e144924
      have b0e144966 : (M.op y x) = (k y x) ∨ x = y := by
        first
        | (have j1 := b0e81515 x y
           grind)
        | (have r₁ := b0e144941
           have r₂ := b0e81515 x y
           grind)
        | exact resolve b0e144941 b0e81515
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81515 b0e144941
      have b0e144976 : (M.op x y) = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e144966
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e144966
        | exact resolve b0e144966 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e144966
      have b0e148844 : (σ (M.op x y)) = (M.op y (σ x)) ∨ (σ x) = (M.op y y) ∨ x = y := by
        first
        | (have i₁ := b0e4249 x
           have i₂ := b0e144976
           grind)
        | exact superpose b0e144976 b0e4249
        | (have j0 := b0e4249 x
           grind)
        | exact resolve b0e4249 b0e144976
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4249 b0e144976
      have b0e148921 : (σ x) = (M.op y y) ∨ x = y := by
        first
        | (have r₁ := b0e148844
           have r₂ := b0e4351
           grind)
        | exact resolve b0e148844 b0e4351
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4351 b0e148844
      have b0e149129 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e86464 y y
           have i₂ := b0e148921
           grind)
        | exact superpose b0e148921 b0e86464
        | exact resolve b0e86464 b0e148921
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e86464 b0e148921
      have b0e149150 : (σ x) = (σ (k x x)) ∨ x = y := by
        first
        | (have i₁ := b0e149129
           have i₂ := b0e15 x x
           grind)
        | exact superpose b0e15 b0e149129
        | exact resolve b0e149129 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e149129
      have b0e149209 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e149150
           have i₂ := b0e141060
           grind)
        | exact superpose b0e141060 b0e149150
        | exact resolve b0e149150 b0e141060
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141060 b0e149150
      have b0e150222 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e11 y
           have i₂ := b0e149209
           grind)
        | exact superpose b0e149209 b0e11
        | exact resolve b0e11 b0e149209
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e149209
      have b0e150320 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e150222
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e150222
        | exact resolve b0e150222 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e150222
      have b0e150321 : x = y := by grind
      clear b0e150320
      have b0e150344 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e150321
           grind)
        | exact superpose b0e150321 b0e16
        | exact resolve b0e16 b0e150321
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e150321
      have b0e150729 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e150344
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e150344
        | exact resolve b0e150344 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e150344
      have b0e150853 : False := by grind
      exact b0e150853
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
        intro X0 X1 X2
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
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
      have b1e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op X1 X2)) = (M.op (M.op X1 X2) (M.op X0 (M.op X0 X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 (M.op X1 X2) X0 X3
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
        | (have i₁ := b1e10 X2 X0 X3
           have i₂ := b1e10 X2 X0 X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e32 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b1e10 X0 x x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e36 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b1e32 x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e32
        | exact resolve b1e32 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e39 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 x X1
           have i₂ := b1e32 X0
           grind)
        | exact superpose b1e32 b1e10
        | exact resolve b1e10 b1e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e46 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e49 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
      have b1e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
      have b1e54 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X0) := by
        intro X0
        first
        | (have i₁ := b1e10 X0 y x
           have i₂ := b1e36
           grind)
        | exact superpose b1e36 b1e10
        | exact resolve b1e10 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e55 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b1e54 X0
           have i₂ := b1e39 X0 y
           grind)
        | exact superpose b1e39 b1e54
        | exact resolve b1e54 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54
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
      have b1e75 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x X0) X1)) = (M.op (M.op X1 X2) (M.op x X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (M.op x X0) X1 X2
           have i₂ := b1e39 (M.op (M.op x X0) X1) X0
           grind)
        | exact superpose b1e39 b1e10
        | exact resolve b1e10 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e80 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op x X0)) = (M.op y (M.op y X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e75 X0 X1 X2
           have i₂ := b1e39 X1 X0
           grind)
        | exact superpose b1e39 b1e75
        | exact resolve b1e75 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e75
      have b1e109 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op X2 X3) X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e31 X2 X3 X4 (M.op X2 X0)
           have i₂ := b1e10 X2 X0 X1
           grind)
        | exact superpose b1e10 b1e31
        | exact resolve b1e31 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e110 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e31 X0 X1 X2 (M.op X0 x)
           have i₂ := b1e32 X0
           grind)
        | exact superpose b1e32 b1e31
        | exact resolve b1e31 b1e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e117 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op x y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e31 y X0 X1 x
           have i₂ := b1e36
           grind)
        | exact superpose b1e36 b1e31
        | exact resolve b1e31 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e36
      have b1e141 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X2) x)) = (M.op y (M.op X0 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e32 (M.op X0 X2)
           have i₂ := b1e31 X0 X2 (M.op (M.op X0 X2) x) X1
           grind)
        | (have i₁ := b1e32 (M.op X0 X2)
           have i₂ := b1e31 X0 X1 (M.op (M.op X0 X2) x) X2
           grind)
        | exact superpose b1e31 b1e32
        | exact resolve b1e32 b1e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e31 b1e32
      have b1e144 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op x (M.op x X0))) = (M.op y (M.op X0 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e141 X0 X1 X2
           have i₂ := b1e10 x X0 X2
           grind)
        | exact superpose b1e10 b1e141
        | exact resolve b1e141 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e141
      have b1e150 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e117 X0 X1
           have i₂ := b1e39 X1 y
           grind)
        | exact superpose b1e39 b1e117
        | exact resolve b1e117 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e39 b1e117
      have b1e152 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op (M.op y (M.op X0 X1)) X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e109 X0 X1 X2 X3 X4
           have i₂ := b1e110 (M.op X0 X1) X2 X4
           grind)
        | exact superpose b1e110 b1e109
        | exact resolve b1e109 b1e110
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e109
      have b1e157 : ∀ X0 X2 : G, (M.op y (M.op y X0)) = (M.op y (M.op X0 X2)) := by
        intro X0 X2
        first
        | (have i₁ := b1e144 X0 x X2
           have i₂ := b1e80 (M.op x X0) X0 x
           grind)
        | exact superpose b1e80 b1e144
        | exact resolve b1e144 b1e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e80 b1e144
      have b1e162 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op (M.op y y) X4) := by
        intro X2 X3 X4
        first
        | (have i₁ := b1e152 x x X2 X3 X4
           have i₂ := b1e110 y (M.op x x) X4
           grind)
        | (have i₁ := b1e152 x x X2 X3 X2
           have i₂ := b1e110 (M.op x x) x X2
           grind)
        | exact superpose b1e110 b1e152
        | exact resolve b1e152 b1e110
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e110 b1e152
      have b1e165 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op y X4) := by
        intro X2 X3 X4
        first
        | (have i₁ := b1e162 X2 X3 X4
           have i₂ := b1e150 y X4
           grind)
        | exact superpose b1e150 b1e162
        | exact resolve b1e162 b1e150
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e150 b1e162
      have b1e184 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 X1 x
           have i₂ := b1e165 X1 x X0
           grind)
        | exact superpose b1e165 b1e10
        | exact resolve b1e10 b1e165
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e224 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e46 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e46
      have b1e880 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b1e49 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e49
      have b1e881 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e880
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e880
        | exact resolve b1e880 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e880
      have b1e882 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e881
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e881
        | exact resolve b1e881 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e881
      have b1e890 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b1e165 (σ x) (σ y) X0
           have i₂ := b1e882
           grind)
        | exact superpose b1e882 b1e165
        | exact resolve b1e165 b1e882
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1603 : (σ y) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e890 (σ x)
           grind)
        | exact superpose b1e890 b1e18
        | exact resolve b1e18 b1e890
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1604 : (σ x) = (M.op y (σ y)) := by
        first
        | (have i₁ := b1e882
           have i₂ := b1e890 (σ y)
           grind)
        | exact superpose b1e890 b1e882
        | exact resolve b1e882 b1e890
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e882
      have b1e1630 : (M.op y (σ x)) = (M.op (σ x) (M.op y y)) := by
        first
        | (have i₁ := b1e55 (σ x)
           have i₂ := b1e890 y
           grind)
        | exact superpose b1e890 b1e55
        | exact resolve b1e55 b1e890
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e55
      have b1e1631 : (M.op y (M.op y y)) = (M.op y (σ x)) := by
        first
        | (have i₁ := b1e1630
           have i₂ := b1e890 (M.op y y)
           grind)
        | exact superpose b1e890 b1e1630
        | exact resolve b1e1630 b1e890
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1630
      have b1e1661 : (M.op y y) = (M.op y (σ x)) := by
        first
        | (have i₁ := b1e1631
           have i₂ := b1e184 y y
           grind)
        | exact superpose b1e184 b1e1631
        | exact resolve b1e1631 b1e184
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1631
      have b1e2264 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 (M.op X0 X0)))) := by
        intro X0 X1
        grind
      clear b1e30
      have b1e2353 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op y (M.op X0 (M.op X0 X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b1e2264 X0 X1
           have i₂ := b1e165 X0 X1 (M.op X0 (M.op X0 X0))
           grind)
        | exact superpose b1e165 b1e2264
        | exact resolve b1e2264 b1e165
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e165 b1e2264
      have b1e2513 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op y (M.op y X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e2353 X0 X1
           have i₂ := b1e157 X0 (M.op X0 X0)
           grind)
        | (have i₁ := b1e2353 y X1
           have i₂ := b1e157 (M.op y y) x
           grind)
        | exact superpose b1e157 b1e2353
        | exact resolve b1e2353 b1e157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e157 b1e2353
      have b1e2663 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op y y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e2513 X0 X1
           have i₂ := b1e184 y X0
           grind)
        | exact superpose b1e184 b1e2513
        | exact resolve b1e2513 b1e184
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e184 b1e2513
      have b1e3201 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e50 x x
           grind)
        | exact superpose b1e50 b1e18
        | (have j1 := b1e50 x x
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e50 x y
           grind)
        | exact resolve b1e18 b1e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e50
      have b1e3287 : (σ x) = (M.op y (σ x)) ∨ (σ y) ≠ (σ (k x x)) := by
        first
        | (have i₁ := b1e3201
           have i₂ := b1e890 (σ x)
           grind)
        | exact superpose b1e890 b1e3201
        | exact resolve b1e3201 b1e890
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e890 b1e3201
      have b1e3326 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op y y) := by
        first
        | (have i₁ := b1e3287
           have i₂ := b1e1661
           grind)
        | exact superpose b1e1661 b1e3287
        | exact resolve b1e3287 b1e1661
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1661 b1e3287
      have b1e3781 : x ≠ y ∨ x = (k x x) := by
        first
        | (have i₁ := b1e224 x x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e224
        | (have j0 := b1e224 x x
           grind)
        | exact resolve b1e224 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e224
      have b1e5931 : (σ x) = (k (σ x) (M.op y y)) := by
        first
        | (have i₁ := b1e2663 y (σ y)
           have i₂ := b1e1604
           grind)
        | exact superpose b1e1604 b1e2663
        | exact resolve b1e2663 b1e1604
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2663
      have b1e5971 : (k x (τ (M.op y y))) = (τ (σ x)) := by
        first
        | (have i₁ := b1e62 x (M.op y y)
           have i₂ := b1e5931
           grind)
        | exact superpose b1e5931 b1e62
        | exact resolve b1e62 b1e5931
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e62 b1e5931
      have b1e5980 : x = (k x (τ (M.op y y))) := by
        first
        | (have i₁ := b1e5971
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e5971
        | exact resolve b1e5971 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5971
      have b1e6004 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op y y) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e3326
           have i₂ := b1e14 x x
           grind)
        | exact superpose b1e14 b1e3326
        | (have j1 := b1e14 y (σ x)
           grind)
        | exact resolve b1e3326 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3326
      have b1e6005 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op y y) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e6004
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e6004
        | exact resolve b1e6004 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6004
      have b1e6006 : (σ x) = (M.op y y) ∨ x = (M.op x x) := by grind
      clear b1e6005
      have b1e6013 : (σ x) = (M.op y y) ∨ x = y := by
        first
        | (have i₁ := b1e6006
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e6006
        | exact resolve b1e6006 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6006
      have b1e6058 : x = (k x (τ (σ x))) ∨ x = y := by
        first
        | (have i₁ := b1e5980
           have i₂ := b1e6013
           grind)
        | exact superpose b1e6013 b1e5980
        | exact resolve b1e5980 b1e6013
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5980 b1e6013
      have b1e6109 : x = (k x x) ∨ x = y := by
        first
        | (have i₁ := b1e6058
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e6058
        | exact resolve b1e6058 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6058
      have b1e6114 : x = (k x x) := by
        first
        | (have r₁ := b1e6109
           have r₂ := b1e3781
           grind)
        | exact resolve b1e6109 b1e3781
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3781 b1e6109
      have b1e6199 : x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e14 x x
           have i₂ := b1e6114
           grind)
        | exact superpose b1e6114 b1e14
        | (have j0 := b1e14 x x
           grind)
        | exact resolve b1e14 b1e6114
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6114
      have b1e6200 : x = (M.op x x) := by grind
      clear b1e6199
      have b1e6213 : x = y := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e6200
           grind)
        | exact superpose b1e6200 b1e17
        | exact resolve b1e17 b1e6200
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6200
      have b1e6339 : (σ x) ≠ (M.op x (σ x)) := by
        first
        | (have i₁ := b1e1603
           have i₂ := b1e6213
           grind)
        | exact superpose b1e6213 b1e1603
        | exact resolve b1e1603 b1e6213
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1603
      have b1e6340 : (σ x) = (M.op x (σ x)) := by
        first
        | (have i₁ := b1e1604
           have i₂ := b1e6213
           grind)
        | exact superpose b1e6213 b1e1604
        | exact resolve b1e1604 b1e6213
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1604 b1e6213
      have b1e6358 : False := by grind
      exact b1e6358
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
      have b2e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X3 X2 (M.op X2 X0)
           have i₂ := b2e10 X2 X0 X1
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e48 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b2e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
      have b2e54 : x = (M.op x y) ∨ y = (M.op x x) := by
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
      have b2e57 : x = (M.op x y) := by
        first
        | (have r₁ := b2e54
           have r₂ := b2e17
           grind)
        | exact resolve b2e54 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54
      have b2e59 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b2e10 X0 x y
           have i₂ := b2e57
           grind)
        | exact superpose b2e57 b2e10
        | exact resolve b2e10 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e93 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op x X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e33 x X0 X1 y
           have i₂ := b2e57
           grind)
        | exact superpose b2e57 b2e33
        | exact resolve b2e33 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e119 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X1) = (M.op (M.op X0 X2) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e33 X0 (M.op X0 x) X1 X2
           have i₂ := b2e59 X0
           grind)
        | exact superpose b2e59 b2e33
        | exact resolve b2e33 b2e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e33
      have b2e121 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) X0) = (M.op X0 (M.op x X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 (M.op X0 x) X1
           have i₂ := b2e59 X0
           grind)
        | exact superpose b2e59 b2e10
        | exact resolve b2e10 b2e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e59
      have b2e126 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op x X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e121 X0 X1
           have i₂ := b2e35 X0 x X1 X0
           grind)
        | exact superpose b2e35 b2e121
        | exact resolve b2e121 b2e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e35 b2e121
      have b2e128 : ∀ X0 X1 X2 : G, (M.op x X1) = (M.op (M.op X0 X2) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e119 X0 X1 X2
           have i₂ := b2e93 X0 X1
           grind)
        | exact superpose b2e93 b2e119
        | exact resolve b2e119 b2e93
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e119
      have b2e190 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X1) = (M.op X1 (M.op X1 (M.op x X2))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 X1 (M.op x X2) X0
           have i₂ := b2e93 X2 X0
           grind)
        | exact superpose b2e93 b2e10
        | exact resolve b2e10 b2e93
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e93
      have b2e202 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op X1 (M.op x X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e190 X0 X1 x
           have i₂ := b2e126 X1 (M.op x x)
           grind)
        | exact superpose b2e126 b2e190
        | exact resolve b2e190 b2e126
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e126 b2e190
      have b2e214 : ∀ X1 : G, (M.op x X1) = (M.op X1 (M.op x X1)) := by
        intro X1
        first
        | (have i₁ := b2e202 x X1
           have i₂ := b2e128 x X1 x
           grind)
        | exact superpose b2e128 b2e202
        | exact resolve b2e202 b2e128
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e128 b2e202
      have b2e876 : x = (M.op y x) := by
        first
        | (have i₁ := b2e214 y
           have i₂ := b2e57
           grind)
        | exact superpose b2e57 b2e214
        | exact resolve b2e214 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e57 b2e214
      have b2e2696 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e52 x x
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e52
        | exact resolve b2e52 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e52
      have b2e3574 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e11 (k x x)
           have i₂ := b2e2696
           grind)
        | exact superpose b2e2696 b2e11
        | exact resolve b2e11 b2e2696
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2696
      have b2e3590 : y = (k x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e3574
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e3574
        | exact resolve b2e3574 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3574
      have b2e4246 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e48 x x
           have i₂ := b2e3590
           grind)
        | exact superpose b2e3590 b2e48
        | exact resolve b2e48 b2e3590
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e48 b2e3590
      have b2e4249 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b2e4246
           have r₂ := b2e17
           grind)
        | exact resolve b2e4246 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4246
      have b2e4321 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b2e11 y
           have i₂ := b2e4249
           grind)
        | exact superpose b2e4249 b2e11
        | exact resolve b2e11 b2e4249
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4249
      have b2e4341 : x = y ∨ x = y := by
        first
        | (have i₁ := b2e4321
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e4321
        | exact resolve b2e4321 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4321
      have b2e4342 : x = y := by grind
      clear b2e4341
      have b2e4416 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e4342
           grind)
        | exact superpose b2e4342 b2e16
        | exact resolve b2e16 b2e4342
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e4425 : x = (M.op x x) := by
        first
        | (have i₁ := b2e876
           have i₂ := b2e4342
           grind)
        | exact superpose b2e4342 b2e876
        | exact resolve b2e876 b2e4342
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e876
      have b2e4433 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e4416
           have i₂ := b2e4425
           grind)
        | exact superpose b2e4425 b2e4416
        | exact resolve b2e4416 b2e4425
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4416 b2e4425
      have b2e4435 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e4433
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e4433
        | exact resolve b2e4433 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4433
      have b2e4436 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b2e4435
           have i₂ := b2e4342
           grind)
        | exact superpose b2e4342 b2e4435
        | exact resolve b2e4435 b2e4342
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4342 b2e4435
      have b2e4437 : False := by grind
      exact b2e4437
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
      have b3e39 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
      have b3e254 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b3e39 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e39
      have b3e255 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e254
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e254
        | exact resolve b3e254 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e254
      have b3e256 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e255
           grind)
        | exact superpose b3e255 b3e16
        | exact resolve b3e16 b3e255
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e255
      have b3e354 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b3e256
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e256
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e256 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e256
      have b3e355 : y = (M.op x x) := by grind
      clear b3e354
      have b3e357 : False := by grind
      exact b3e357

/-- `Equation4411`: `x ◇ (x ◇ y) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation4411 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4411 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4411.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
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
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op x x) := by grind
      have b0e18 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
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
      have b0e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X2 (M.op X2 X0) X3
           have i₂ := b0e10 X2 X0 X1
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X2 X0 X3
           have i₂ := b0e10 X2 X0 X1
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X3 X2 (M.op X2 X0)
           have i₂ := b0e10 X2 X0 X1
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (M.op (σ y) X0) := by
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
      have b0e38 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op y X0) := by
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
      have b0e39 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 (M.op X2 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e31 X0 X1 X2 X3
           have i₂ := b0e35 X2 X0 X3 X2
           grind)
        | exact superpose b0e35 b0e31
        | exact resolve b0e31 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e41 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e38 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e38
        | exact resolve b0e38 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 x X1
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e10
        | exact resolve b0e10 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) X0) = (M.op X0 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 (M.op X0 x) X1
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e10
        | exact resolve b0e10 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e45 X0 X1
           have i₂ := b0e35 X0 x X1 X0
           grind)
        | exact superpose b0e35 b0e45
        | exact resolve b0e45 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e45
      have b0e51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e52 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X2)) ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 X2 X2
           have i₂ := b0e14 X2 X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op X1 X2)
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X2 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e14 (σ X1) (σ X0)
           grind)
        | exact superpose b0e14 b0e15
        | (have j1 := b0e14 (σ X1) (σ X0)
           grind)
        | exact resolve b0e15 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e113 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op X2 X3) X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e34 X2 X3 X4 (M.op X2 X0)
           have i₂ := b0e10 X2 X0 X1
           grind)
        | exact superpose b0e10 b0e34
        | exact resolve b0e34 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e114 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e34 X0 X1 X2 (M.op X0 x)
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e34
        | exact resolve b0e34 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e122 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op x y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e34 y X0 X1 x
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e34
        | exact resolve b0e34 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34 b0e41
      have b0e155 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e122 X0 X1
           have i₂ := b0e43 X1 y
           grind)
        | exact superpose b0e43 b0e122
        | exact resolve b0e122 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e122
      have b0e157 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op (M.op y (M.op X0 X1)) X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e113 X0 X1 X2 X3 X4
           have i₂ := b0e114 (M.op X0 X1) X2 X4
           grind)
        | exact superpose b0e114 b0e113
        | exact resolve b0e113 b0e114
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e113
      have b0e167 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op (M.op y y) X4) := by
        intro X2 X3 X4
        first
        | (have i₁ := b0e157 x x X2 X3 X4
           have i₂ := b0e114 y (M.op x x) X4
           grind)
        | (have i₁ := b0e157 x x X2 X3 X2
           have i₂ := b0e114 (M.op x x) x X2
           grind)
        | exact superpose b0e114 b0e157
        | exact resolve b0e157 b0e114
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e114 b0e157
      have b0e170 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op y X4) := by
        intro X2 X3 X4
        first
        | (have i₁ := b0e167 X2 X3 X4
           have i₂ := b0e155 y X4
           grind)
        | exact superpose b0e155 b0e167
        | exact resolve b0e167 b0e155
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e155 b0e167
      have b0e180 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e170 (σ x) (σ x) X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e170
        | exact resolve b0e170 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e199 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op y x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e38 (M.op X0 X1)
           have i₂ := b0e170 X0 X1 x
           grind)
        | exact superpose b0e170 b0e38
        | exact resolve b0e38 b0e170
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e200 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y (M.op y x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e199 X0 X1
           have i₂ := b0e170 X0 X1 (M.op y x)
           grind)
        | exact superpose b0e170 b0e199
        | exact resolve b0e199 b0e170
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e199
      have b0e209 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y y) := by
        intro X0 X1
        first
        | (have i₁ := b0e200 X0 X1
           have i₂ := b0e38 y
           grind)
        | exact superpose b0e38 b0e200
        | exact resolve b0e200 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e200
      have b0e228 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
      have b0e257 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
        first
        | (have i₁ := b0e228
           have i₂ := b0e180 (σ x)
           grind)
        | exact superpose b0e180 b0e228
        | exact resolve b0e228 b0e180
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e180 b0e228
      have b0e367 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e51 (σ X1) (σ X0)
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e51
        | exact resolve b0e51 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e369 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e24 X0 X1
           have i₂ := b0e51 (τ X0) X1
           grind)
        | exact superpose b0e51 b0e24
        | (have j1 := b0e51 (τ X0) X1
           grind)
        | exact resolve b0e24 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24
      have b0e373 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e51 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51
      have b0e861 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X0) = (M.op X0 (M.op (M.op X1 X2) X0)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e10 X0 X3 X4
           have i₂ := b0e39 X1 X2 X0 X3
           grind)
        | (have i₁ := b0e10 (M.op X0 X1) (M.op X0 X1) X2
           have i₂ := b0e39 X0 X1 (M.op X0 X1) X3
           grind)
        | exact superpose b0e39 b0e10
        | exact resolve b0e10 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e885 : ∀ X0 X3 X4 : G, (M.op X0 (M.op y X0)) = (M.op (M.op X3 X4) X0) := by
        intro X0 X3 X4
        first
        | (have i₁ := b0e861 X0 x x X3 X4
           have i₂ := b0e170 x x X0
           grind)
        | exact superpose b0e170 b0e861
        | exact resolve b0e861 b0e170
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e861
      have b0e945 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e885 X0 x x
           have i₂ := b0e170 x x X0
           grind)
        | exact superpose b0e170 b0e885
        | exact resolve b0e885 b0e170
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e170 b0e885
      have b0e1981 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) X2) = (M.op X2 (M.op X2 (σ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e52 (σ X0) X2 (σ X1)
           grind)
        | exact superpose b0e52 b0e15
        | (have j1 := b0e52 (σ X0) X2 (σ X1)
           grind)
        | exact resolve b0e15 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52
      have b0e1984 : ∀ X0 X1 X2 : G, (M.op X2 (M.op y X2)) = (M.op (σ X0) X2) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1981 X0 X1 X2
           have i₂ := b0e46 X2 (σ X1)
           grind)
        | exact superpose b0e46 b0e1981
        | (have j0 := b0e1981 X0 X1 X2
           grind)
        | exact resolve b0e1981 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e1981
      have b0e2075 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (σ X0) X2) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1984 X0 X1 X2
           have i₂ := b0e945 X2
           grind)
        | exact superpose b0e945 b0e1984
        | (have j0 := b0e1984 X0 X1 X2
           grind)
        | exact resolve b0e1984 b0e945
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1984
      have b0e4126 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1
           have i₂ := b0e55 X1 X0
           grind)
        | exact superpose b0e55 b0e11
        | (have j1 := b0e55 X1 X0
           grind)
        | exact resolve b0e11 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e4319 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e257
           grind)
        | exact superpose b0e257 b0e16
        | exact resolve b0e16 b0e257
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e4370 : ∀ X0 : G, (M.op y X0) ≠ (M.op y X0) ∨ (M.op y X0) = (k (M.op y X0) X0) := by
        intro X0
        first
        | (have i₁ := b0e373 (M.op y X0) X0
           have i₂ := b0e945 X0
           grind)
        | exact superpose b0e945 b0e373
        | (have j0 := b0e373 (M.op y X0) X0
           grind)
        | (have r₁ := b0e373 (M.op y X0) X0
           have r₂ := b0e945 X0
           grind)
        | exact resolve b0e373 b0e945
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e373 b0e945
      have b0e4397 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) X0) := by
        intro X0
        first
        | (have j0 := b0e4370 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4370
      have b0e4918 : ∀ X0 X1 : G, (M.op y y) = (k (M.op y y) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e4397 (M.op X0 X1)
           have i₂ := b0e209 X0 X1
           grind)
        | exact superpose b0e209 b0e4397
        | exact resolve b0e4397 b0e209
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e209 b0e4397
      have b0e13515 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e369 (σ X0) X1
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e369
        | exact resolve b0e369 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e369
      have b0e13581 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e13515 X0 X1
           have i₂ := b0e15 X1 X0
           grind)
        | exact superpose b0e15 b0e13515
        | (have j0 := b0e13515 X0 X1
           grind)
        | exact resolve b0e13515 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13515
      have b0e22433 : (M.op y (σ x)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
        first
        | (have i₁ := b0e257
           have i₂ := b0e367 y x
           grind)
        | exact superpose b0e367 b0e257
        | (have j1 := b0e367 y x
           grind)
        | exact resolve b0e257 b0e367
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e367
      have b0e26004 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ y) = (M.op y (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e2075 x X0 (σ x)
           grind)
        | exact superpose b0e2075 b0e18
        | (have j1 := b0e2075 x X0 x
           grind)
        | exact resolve b0e18 b0e2075
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2075
      have b0e26969 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) := by
        first
        | (have i₁ := b0e4126 x x
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e4126
        | exact resolve b0e4126 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4126
      have b0e27099 : (σ y) = (σ (k x x)) ∨ x = y := by
        first
        | (have i₁ := b0e26969
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e26969
        | exact resolve b0e26969 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26969
      have b0e27230 : (k x x) = (τ (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e11 (k x x)
           have i₂ := b0e27099
           grind)
        | exact superpose b0e27099 b0e11
        | exact resolve b0e11 b0e27099
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27099
      have b0e27279 : y = (k x x) ∨ x = y := by
        first
        | (have i₁ := b0e27230
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e27230
        | exact resolve b0e27230 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27230
      have b0e92636 : (σ (M.op x y)) = (M.op y (σ x)) ∨ y = (k y x) ∨ (σ y) = (σ (k y x)) := by
        first
        | (have i₁ := b0e13581 x y
           have i₂ := b0e22433
           grind)
        | exact superpose b0e22433 b0e13581
        | (have j0 := b0e13581 x y
           grind)
        | exact resolve b0e13581 b0e22433
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13581 b0e22433
      have b0e92809 : (σ y) = (σ (k y x)) ∨ y = (k y x) := by
        first
        | (have r₁ := b0e92636
           have r₂ := b0e4319
           grind)
        | exact resolve b0e92636 b0e4319
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e92636
      have b0e93021 : (k y x) = (τ (σ y)) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e11 (k y x)
           have i₂ := b0e92809
           grind)
        | exact superpose b0e92809 b0e11
        | exact resolve b0e11 b0e92809
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e92809
      have b0e93207 : y = (k y x) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e93021
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e93021
        | exact resolve b0e93021 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e93021
      have b0e93208 : y = (k y x) := by grind
      clear b0e93207
      have b0e93325 : x = (M.op y y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e93208
           grind)
        | exact superpose b0e93208 b0e14
        | (have j0 := b0e14 y x
           grind)
        | exact resolve b0e14 b0e93208
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e93877 : x = (k x x) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e4918 y y
           have i₂ := b0e93325
           grind)
        | exact superpose b0e93325 b0e4918
        | exact resolve b0e4918 b0e93325
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4918 b0e93325
      have b0e95147 : x = y ∨ x = y ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e27279
           have i₂ := b0e93877
           grind)
        | exact superpose b0e93877 b0e27279
        | exact resolve b0e27279 b0e93877
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27279 b0e93877
      have b0e95201 : y = (M.op x y) ∨ x = y := by grind
      clear b0e95147
      have b0e95657 : (σ y) ≠ (M.op y (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e4319
           have i₂ := b0e95201
           grind)
        | exact superpose b0e95201 b0e4319
        | exact resolve b0e4319 b0e95201
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4319 b0e95201
      have b0e101410 : (M.op y (σ x)) = (σ (k y x)) ∨ (σ y) = (M.op y (σ x)) := by
        first
        | (have i₁ := b0e257
           have i₂ := b0e26004 y
           grind)
        | exact superpose b0e26004 b0e257
        | exact resolve b0e257 b0e26004
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e257 b0e26004
      have b0e101571 : (σ y) = (M.op y (σ x)) ∨ (σ y) = (M.op y (σ x)) := by
        first
        | (have i₁ := b0e101410
           have i₂ := b0e93208
           grind)
        | exact superpose b0e93208 b0e101410
        | exact resolve b0e101410 b0e93208
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e93208 b0e101410
      have b0e101572 : (σ y) = (M.op y (σ x)) := by grind
      clear b0e101571
      have b0e101647 : (σ y) ≠ (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e95657
           have i₂ := b0e101572
           grind)
        | exact superpose b0e101572 b0e95657
        | (have r₁ := b0e95657
           have r₂ := b0e101572
           grind)
        | exact resolve b0e95657 b0e101572
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e95657 b0e101572
      have b0e101727 : x = y := by grind
      clear b0e101647
      have b0e103667 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e101727
           grind)
        | exact superpose b0e101727 b0e16
        | exact resolve b0e16 b0e101727
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e101727
      have b0e103802 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e103667
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e103667
        | exact resolve b0e103667 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e103667
      have b0e103825 : False := by grind
      exact b0e103825
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
        intro X0 X1 X2
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
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
      have b1e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op X1 X2)) = (M.op (M.op X1 X2) (M.op X0 (M.op X0 X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 (M.op X1 X2) X0 X3
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
        | (have i₁ := b1e10 X2 X0 X3
           have i₂ := b1e10 X2 X0 X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e32 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b1e10 X0 x x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e36 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b1e32 x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e32
        | exact resolve b1e32 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e39 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 x X1
           have i₂ := b1e32 X0
           grind)
        | exact superpose b1e32 b1e10
        | exact resolve b1e10 b1e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e40 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X1 X0 (M.op X0 x)
           have i₂ := b1e32 X0
           grind)
        | exact superpose b1e32 b1e10
        | exact resolve b1e10 b1e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e46 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e49 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
      have b1e50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
      have b1e54 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X0) := by
        intro X0
        first
        | (have i₁ := b1e10 X0 y x
           have i₂ := b1e36
           grind)
        | exact superpose b1e36 b1e10
        | exact resolve b1e10 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e55 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b1e54 X0
           have i₂ := b1e39 X0 y
           grind)
        | exact superpose b1e39 b1e54
        | exact resolve b1e54 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54
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
      have b1e75 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x X0) X1)) = (M.op (M.op X1 X2) (M.op x X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (M.op x X0) X1 X2
           have i₂ := b1e39 (M.op (M.op x X0) X1) X0
           grind)
        | exact superpose b1e39 b1e10
        | exact resolve b1e10 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e80 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op x X0)) = (M.op y (M.op y X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e75 X0 X1 X2
           have i₂ := b1e39 X1 X0
           grind)
        | exact superpose b1e39 b1e75
        | exact resolve b1e75 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e75
      have b1e107 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op X2 X3) X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e31 X2 X3 X4 (M.op X2 X0)
           have i₂ := b1e10 X2 X0 X1
           grind)
        | exact superpose b1e10 b1e31
        | exact resolve b1e31 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e108 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e31 X0 X1 X2 (M.op X0 x)
           have i₂ := b1e32 X0
           grind)
        | exact superpose b1e32 b1e31
        | exact resolve b1e31 b1e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e115 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op x y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e31 y X0 X1 x
           have i₂ := b1e36
           grind)
        | exact superpose b1e36 b1e31
        | exact resolve b1e31 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e36
      have b1e139 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X2) x)) = (M.op y (M.op X0 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e32 (M.op X0 X2)
           have i₂ := b1e31 X0 X2 (M.op (M.op X0 X2) x) X1
           grind)
        | (have i₁ := b1e32 (M.op X0 X2)
           have i₂ := b1e31 X0 X1 (M.op (M.op X0 X2) x) X2
           grind)
        | exact superpose b1e31 b1e32
        | exact resolve b1e32 b1e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e31 b1e32
      have b1e142 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op x (M.op x X0))) = (M.op y (M.op X0 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e139 X0 X1 X2
           have i₂ := b1e10 x X0 X2
           grind)
        | exact superpose b1e10 b1e139
        | exact resolve b1e139 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e139
      have b1e148 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e115 X0 X1
           have i₂ := b1e39 X1 y
           grind)
        | exact superpose b1e39 b1e115
        | exact resolve b1e115 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e39 b1e115
      have b1e150 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op (M.op y (M.op X0 X1)) X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e107 X0 X1 X2 X3 X4
           have i₂ := b1e108 (M.op X0 X1) X2 X4
           grind)
        | exact superpose b1e108 b1e107
        | exact resolve b1e107 b1e108
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e107
      have b1e155 : ∀ X0 X2 : G, (M.op y (M.op y X0)) = (M.op y (M.op X0 X2)) := by
        intro X0 X2
        first
        | (have i₁ := b1e142 X0 x X2
           have i₂ := b1e80 (M.op x X0) X0 x
           grind)
        | exact superpose b1e80 b1e142
        | exact resolve b1e142 b1e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e80 b1e142
      have b1e160 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op (M.op y y) X4) := by
        intro X2 X3 X4
        first
        | (have i₁ := b1e150 x x X2 X3 X4
           have i₂ := b1e108 y (M.op x x) X4
           grind)
        | (have i₁ := b1e150 x x X2 X3 X2
           have i₂ := b1e108 (M.op x x) x X2
           grind)
        | exact superpose b1e108 b1e150
        | exact resolve b1e150 b1e108
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e150
      have b1e163 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op y X4) := by
        intro X2 X3 X4
        first
        | (have i₁ := b1e160 X2 X3 X4
           have i₂ := b1e148 y X4
           grind)
        | exact superpose b1e148 b1e160
        | exact resolve b1e160 b1e148
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e148 b1e160
      have b1e182 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 X1 x
           have i₂ := b1e163 X1 x X0
           grind)
        | exact superpose b1e163 b1e10
        | exact resolve b1e10 b1e163
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e220 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e46 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e46
      have b1e876 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have j0 := b1e49 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e49
      have b1e877 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e876
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e876
        | exact resolve b1e876 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e876
      have b1e878 : (σ x) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e877
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e877
        | exact resolve b1e877 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e877
      have b1e879 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op (σ x) X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e10 (σ y) (σ x) X0
           have i₂ := b1e878
           grind)
        | exact superpose b1e878 b1e10
        | exact resolve b1e10 b1e878
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e885 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b1e163 (σ y) (σ x) X0
           have i₂ := b1e878
           grind)
        | exact superpose b1e878 b1e163
        | exact resolve b1e163 b1e878
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e891 : (M.op (σ y) (σ x)) = (M.op (M.op y (σ x)) (σ y)) := by
        first
        | (have i₁ := b1e879 x
           have i₂ := b1e108 (σ x) x (σ y)
           grind)
        | exact superpose b1e108 b1e879
        | exact resolve b1e879 b1e108
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e108 b1e879
      have b1e895 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) y)) := by
        first
        | (have i₁ := b1e891
           have i₂ := b1e10 (σ y) y (σ x)
           grind)
        | exact superpose b1e10 b1e891
        | exact resolve b1e891 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e891
      have b1e898 : (M.op (σ y) (σ x)) = (M.op (M.op y y) (σ y)) := by
        first
        | (have i₁ := b1e895
           have i₂ := b1e40 y (σ y)
           grind)
        | exact superpose b1e40 b1e895
        | exact resolve b1e895 b1e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e40 b1e895
      have b1e899 : (M.op (σ y) (σ x)) = (M.op y (σ y)) := by
        first
        | (have i₁ := b1e898
           have i₂ := b1e163 y y (σ y)
           grind)
        | exact superpose b1e163 b1e898
        | exact resolve b1e898 b1e163
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e898
      have b1e900 : (σ x) = (M.op y (σ y)) := by
        first
        | (have i₁ := b1e899
           have i₂ := b1e878
           grind)
        | exact superpose b1e878 b1e899
        | exact resolve b1e899 b1e878
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e878 b1e899
      have b1e1614 : (σ y) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e885 (σ x)
           grind)
        | exact superpose b1e885 b1e18
        | exact resolve b1e18 b1e885
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1640 : (M.op y (σ x)) = (M.op (σ x) (M.op y y)) := by
        first
        | (have i₁ := b1e55 (σ x)
           have i₂ := b1e885 y
           grind)
        | exact superpose b1e885 b1e55
        | exact resolve b1e55 b1e885
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e55
      have b1e1641 : (M.op y (M.op y y)) = (M.op y (σ x)) := by
        first
        | (have i₁ := b1e1640
           have i₂ := b1e885 (M.op y y)
           grind)
        | exact superpose b1e885 b1e1640
        | exact resolve b1e1640 b1e885
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1640
      have b1e1670 : (M.op y y) = (M.op y (σ x)) := by
        first
        | (have i₁ := b1e1641
           have i₂ := b1e182 y y
           grind)
        | exact superpose b1e182 b1e1641
        | exact resolve b1e1641 b1e182
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1641
      have b1e2253 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 (M.op X0 X0)))) := by
        intro X0 X1
        grind
      clear b1e30
      have b1e2342 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op y (M.op X0 (M.op X0 X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b1e2253 X0 X1
           have i₂ := b1e163 X0 X1 (M.op X0 (M.op X0 X0))
           grind)
        | exact superpose b1e163 b1e2253
        | exact resolve b1e2253 b1e163
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e163 b1e2253
      have b1e2504 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op y (M.op y X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e2342 X0 X1
           have i₂ := b1e155 X0 (M.op X0 X0)
           grind)
        | (have i₁ := b1e2342 y X1
           have i₂ := b1e155 (M.op y y) x
           grind)
        | exact superpose b1e155 b1e2342
        | exact resolve b1e2342 b1e155
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e155 b1e2342
      have b1e2656 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op y y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e2504 X0 X1
           have i₂ := b1e182 y X0
           grind)
        | exact superpose b1e182 b1e2504
        | exact resolve b1e2504 b1e182
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e182 b1e2504
      have b1e3165 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e50 x x
           grind)
        | exact superpose b1e50 b1e18
        | (have j1 := b1e50 x x
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e50 y x
           grind)
        | exact resolve b1e18 b1e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e50
      have b1e3248 : (σ x) = (M.op y (σ x)) ∨ (σ y) ≠ (σ (k x x)) := by
        first
        | (have i₁ := b1e3165
           have i₂ := b1e885 (σ x)
           grind)
        | exact superpose b1e885 b1e3165
        | exact resolve b1e3165 b1e885
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e885 b1e3165
      have b1e3287 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op y y) := by
        first
        | (have i₁ := b1e3248
           have i₂ := b1e1670
           grind)
        | exact superpose b1e1670 b1e3248
        | exact resolve b1e3248 b1e1670
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1670 b1e3248
      have b1e3893 : x ≠ y ∨ x = (k x x) := by
        first
        | (have i₁ := b1e220 x x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e220
        | (have j0 := b1e220 x x
           grind)
        | exact resolve b1e220 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e220
      have b1e5860 : (σ x) = (k (σ x) (M.op y y)) := by
        first
        | (have i₁ := b1e2656 y (σ y)
           have i₂ := b1e900
           grind)
        | exact superpose b1e900 b1e2656
        | exact resolve b1e2656 b1e900
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2656
      have b1e5888 : (k x (τ (M.op y y))) = (τ (σ x)) := by
        first
        | (have i₁ := b1e62 x (M.op y y)
           have i₂ := b1e5860
           grind)
        | exact superpose b1e5860 b1e62
        | exact resolve b1e62 b1e5860
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e62 b1e5860
      have b1e5897 : x = (k x (τ (M.op y y))) := by
        first
        | (have i₁ := b1e5888
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e5888
        | exact resolve b1e5888 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5888
      have b1e5917 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op y y) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e3287
           have i₂ := b1e14 x x
           grind)
        | exact superpose b1e14 b1e3287
        | (have j1 := b1e14 y (σ x)
           grind)
        | exact resolve b1e3287 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3287
      have b1e5918 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op y y) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e5917
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e5917
        | exact resolve b1e5917 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5917
      have b1e5919 : (σ x) = (M.op y y) ∨ x = (M.op x x) := by grind
      clear b1e5918
      have b1e5926 : (σ x) = (M.op y y) ∨ x = y := by
        first
        | (have i₁ := b1e5919
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e5919
        | exact resolve b1e5919 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5919
      have b1e5973 : x = (k x (τ (σ x))) ∨ x = y := by
        first
        | (have i₁ := b1e5897
           have i₂ := b1e5926
           grind)
        | exact superpose b1e5926 b1e5897
        | exact resolve b1e5897 b1e5926
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5897 b1e5926
      have b1e6025 : x = (k x x) ∨ x = y := by
        first
        | (have i₁ := b1e5973
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e5973
        | exact resolve b1e5973 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5973
      have b1e6030 : x = (k x x) := by
        first
        | (have r₁ := b1e6025
           have r₂ := b1e3893
           grind)
        | exact resolve b1e6025 b1e3893
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3893 b1e6025
      have b1e6096 : x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e14 x x
           have i₂ := b1e6030
           grind)
        | exact superpose b1e6030 b1e14
        | (have j0 := b1e14 x x
           grind)
        | exact resolve b1e14 b1e6030
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6030
      have b1e6097 : x = (M.op x x) := by grind
      clear b1e6096
      have b1e6162 : x = y := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e6097
           grind)
        | exact superpose b1e6097 b1e17
        | exact resolve b1e17 b1e6097
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6097
      have b1e6614 : (σ x) = (M.op x (σ x)) := by
        first
        | (have i₁ := b1e900
           have i₂ := b1e6162
           grind)
        | exact superpose b1e6162 b1e900
        | exact resolve b1e900 b1e6162
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e900
      have b1e6615 : (σ x) ≠ (M.op x (σ x)) := by
        first
        | (have i₁ := b1e1614
           have i₂ := b1e6162
           grind)
        | exact superpose b1e6162 b1e1614
        | exact resolve b1e1614 b1e6162
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1614 b1e6162
      have b1e6633 : False := by grind
      exact b1e6633
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
      have b2e48 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b2e52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
      have b2e54 : x = (M.op y x) ∨ y = (M.op x x) := by
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
      have b2e57 : x = (M.op y x) := by
        first
        | (have r₁ := b2e54
           have r₂ := b2e17
           grind)
        | exact resolve b2e54 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54
      have b2e59 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b2e10 X0 y x
           have i₂ := b2e57
           grind)
        | exact superpose b2e57 b2e10
        | exact resolve b2e10 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e93 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e33 y X0 X1 x
           have i₂ := b2e57
           grind)
        | exact superpose b2e57 b2e33
        | exact resolve b2e33 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e119 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (M.op (M.op x X0) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e33 X0 (M.op X0 y) X1 X2
           have i₂ := b2e59 X0
           grind)
        | exact superpose b2e59 b2e33
        | exact resolve b2e33 b2e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e33
      have b2e156 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) := by
        intro X0
        first
        | (have i₁ := b2e93 (M.op y y) X0
           have i₂ := b2e59 y
           grind)
        | exact superpose b2e59 b2e93
        | exact resolve b2e93 b2e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e59 b2e93
      have b2e192 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x x) X0) := by
        intro X0
        first
        | (have i₁ := b2e156 X0
           have i₂ := b2e119 x X0 y
           grind)
        | (have i₁ := b2e156 x
           have i₂ := b2e119 y x x
           grind)
        | exact superpose b2e119 b2e156
        | exact resolve b2e156 b2e119
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e119 b2e156
      have b2e235 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b2e10 X0 x x
           have i₂ := b2e192 X0
           grind)
        | exact superpose b2e192 b2e10
        | exact resolve b2e10 b2e192
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e192
      have b2e2629 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b2e235 y
           have i₂ := b2e57
           grind)
        | exact superpose b2e57 b2e235
        | exact resolve b2e235 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e235
      have b2e2697 : x = (M.op x y) := by
        first
        | (have i₁ := b2e2629
           have i₂ := b2e57
           grind)
        | exact superpose b2e57 b2e2629
        | exact resolve b2e2629 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e57 b2e2629
      have b2e2773 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e52 x x
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e52
        | exact resolve b2e52 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e52
      have b2e7111 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e11 (k x x)
           have i₂ := b2e2773
           grind)
        | exact superpose b2e2773 b2e11
        | exact resolve b2e11 b2e2773
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2773
      have b2e7128 : y = (k x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e7111
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e7111
        | exact resolve b2e7111 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e7111
      have b2e7138 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e48 x x
           have i₂ := b2e7128
           grind)
        | exact superpose b2e7128 b2e48
        | exact resolve b2e48 b2e7128
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e48 b2e7128
      have b2e7141 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b2e7138
           have r₂ := b2e17
           grind)
        | exact resolve b2e7138 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e7138
      have b2e8126 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b2e11 y
           have i₂ := b2e7141
           grind)
        | exact superpose b2e7141 b2e11
        | exact resolve b2e11 b2e7141
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e7141
      have b2e8142 : x = y ∨ x = y := by
        first
        | (have i₁ := b2e8126
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e8126
        | exact resolve b2e8126 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e8126
      have b2e8143 : x = y := by grind
      clear b2e8142
      have b2e8595 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e8143
           grind)
        | exact superpose b2e8143 b2e16
        | exact resolve b2e16 b2e8143
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e8611 : x = (M.op x x) := by
        first
        | (have i₁ := b2e2697
           have i₂ := b2e8143
           grind)
        | exact superpose b2e8143 b2e2697
        | exact resolve b2e2697 b2e8143
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2697
      have b2e8619 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e8595
           have i₂ := b2e8611
           grind)
        | exact superpose b2e8611 b2e8595
        | exact resolve b2e8595 b2e8611
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e8595 b2e8611
      have b2e8621 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e8619
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e8619
        | exact resolve b2e8619 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e8619
      have b2e8622 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b2e8621
           have i₂ := b2e8143
           grind)
        | exact superpose b2e8143 b2e8621
        | exact resolve b2e8621 b2e8143
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e8143 b2e8621
      have b2e8623 : False := by grind
      exact b2e8623
    · have b3e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
        intro X0 X1 X2
        grind
      have b3e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b3e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b3e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x x) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e20 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b3e21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e15
        | exact resolve b3e15 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e22 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 X2 (M.op X2 X0) X3
           have i₂ := b3e10 X2 X0 X1
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e25 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 X3 X2 (M.op X2 X0)
           have i₂ := b3e10 X2 X0 X1
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e27 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 (M.op X2 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e22 X0 X1 X2 X3
           have i₂ := b3e25 X2 X0 X3 X2
           grind)
        | exact superpose b3e25 b3e22
        | exact resolve b3e22 b3e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e22 b3e25
      have b3e29 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
        intro X0
        grind
      have b3e33 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b3e29 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e29
        | exact resolve b3e29 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e29
      have b3e36 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b3e39 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
      have b3e40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
      have b3e43 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e21 X0 X1
           have i₂ := b3e14 X1 (τ X0)
           grind)
        | exact superpose b3e14 b3e21
        | (have j1 := b3e14 X1 (τ X0)
           grind)
        | exact resolve b3e21 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e48 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k X0 (τ X1))
           have i₂ := b3e21 X1 X0
           grind)
        | exact superpose b3e21 b3e11
        | exact resolve b3e11 b3e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e21
      have b3e92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e36 (σ X1) (σ X0)
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e36
        | exact resolve b3e36 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e98 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b3e36 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e103 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e33 X1
           have i₂ := b3e14 (τ X1) X0
           grind)
        | (have i₁ := b3e33 X0
           have i₂ := b3e14 X0 (M.op (τ X0) (τ X0))
           grind)
        | exact superpose b3e14 b3e33
        | (have j1 := b3e14 (τ X1) X0
           grind)
        | exact resolve b3e33 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e168 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b3e48
      have b3e182 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b3e168 X0
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e168
        | exact resolve b3e168 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e168
      have b3e204 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X4)) := by
        intro X0 X1 X4
        first
        | (have i₁ := b3e27 x x X0 X4
           have i₂ := b3e27 x x X0 X1
           grind)
        | (have i₁ := b3e27 X0 X1 (M.op X0 X1) x
           have i₂ := b3e27 X0 X1 (M.op X0 X1) (M.op X0 X1)
           grind)
        | exact superpose b3e27 b3e27
        | exact resolve b3e27 b3e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e237 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X0) = (M.op X0 (M.op (M.op X1 X2) X0)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e10 X0 X3 X4
           have i₂ := b3e27 X1 X2 X0 X3
           grind)
        | (have i₁ := b3e10 (M.op X0 X1) (M.op X0 X1) X2
           have i₂ := b3e27 X0 X1 (M.op X0 X1) X3
           grind)
        | exact superpose b3e27 b3e10
        | exact resolve b3e10 b3e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e27
      have b3e256 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have j0 := b3e39 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e39
      have b3e257 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e256
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e256
        | exact resolve b3e256 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e256
      have b3e682 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 X0 X2 X3
           have i₂ := b3e204 X0 X2 X1
           grind)
        | (have i₁ := b3e10 X0 X2 X3
           have i₂ := b3e204 X0 X1 X2
           grind)
        | exact superpose b3e204 b3e10
        | exact resolve b3e10 b3e204
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e965 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X4) X2) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e10 X2 X3 X4
           have i₂ := b3e682 X2 X3 X0 X1
           grind)
        | exact superpose b3e682 b3e10
        | exact resolve b3e10 b3e682
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1290 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e40 X1 X1
           have i₂ := b3e40 X0 X1
           grind)
        | exact superpose b3e40 b3e40
        | (have j0 := b3e40 X0 X1
           have j1 := b3e40 X0 X1
           grind)
        | exact resolve b3e40 b3e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1291 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e40 X0 X0
           have i₂ := b3e14 (σ X0) X1
           grind)
        | (have i₁ := b3e40 X0 X1
           have i₂ := b3e14 X0 (M.op (σ X0) (σ X1))
           grind)
        | exact superpose b3e14 b3e40
        | (have j1 := b3e14 (σ X1) X0
           grind)
        | exact resolve b3e40 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1344 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e182 X1
           have i₂ := b3e40 X0 X1
           grind)
        | exact superpose b3e40 b3e182
        | (have j1 := b3e40 X0 X1
           grind)
        | exact resolve b3e182 b3e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e182
      have b3e1368 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b3e40 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e40
      have b3e1371 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e1344 X0 X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e1344
        | (have j0 := b3e1344 X0 X1
           grind)
        | exact resolve b3e1344 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1344
      have b3e3509 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X3 X4) X2) ∨ (M.op (M.op X3 X4) X2) = (k (M.op (M.op X3 X4) X2) X2) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e98 (M.op (M.op X3 X4) X2) X2
           have i₂ := b3e237 X2 X3 X4 X0 X1
           grind)
        | exact superpose b3e237 b3e98
        | (have j0 := b3e98 (M.op (M.op X3 X4) X2) X2
           grind)
        | (have r₁ := b3e98 (M.op (M.op X3 X4) X0) X0
           have r₂ := b3e237 X0 X3 X4 X3 X4
           grind)
        | exact resolve b3e98 b3e237
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e98 b3e237
      have b3e3552 : ∀ X2 X3 X4 : G, (M.op (M.op X3 X4) X2) = (k (M.op (M.op X3 X4) X2) X2) := by
        intro X2 X3 X4
        first
        | (have j0 := b3e3509 x x X2 X3 X4
           grind)
        | (have r₁ := b3e3509 x x X2 X3 X4
           have r₂ := b3e965 x x X2 X3 X4
           grind)
        | (have r₁ := b3e3509 X3 X4 X2 x x
           have r₂ := b3e965 x x X2 X3 X4
           grind)
        | exact resolve b3e3509 b3e965
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e3509
      have b3e5758 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k (M.op X0 X2) X2) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e3552 X2 X0 X0
           have i₂ := b3e14 X0 X1
           grind)
        | (have i₁ := b3e3552 X2 x x
           have i₂ := b3e14 X0 (M.op x x)
           grind)
        | exact superpose b3e14 b3e3552
        | (have j1 := b3e14 X1 X0
           grind)
        | exact resolve b3e3552 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e3552
      have b3e12113 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e43 (σ X0) X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e43
        | exact resolve b3e43 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e12170 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e12 X1
           have i₂ := b3e43 X1 X0
           grind)
        | exact superpose b3e43 b3e12
        | (have j1 := b3e43 X1 X0
           grind)
        | exact resolve b3e12 b3e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e43
      have b3e12349 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e12113 X0 X1
           have i₂ := b3e15 X1 X0
           grind)
        | exact superpose b3e15 b3e12113
        | (have j0 := b3e12113 X0 X1
           grind)
        | exact resolve b3e12113 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e12113
      have b3e14027 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b3e14146 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (σ (k (τ X1) X0)) = (σ (M.op X0 (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e33 X1
           have i₂ := b3e12349 X0 (τ X1)
           grind)
        | (have i₁ := b3e33 X0
           have i₂ := b3e12349 (M.op (τ X0) (τ X0)) X1
           grind)
        | exact superpose b3e12349 b3e33
        | (have j1 := b3e12349 X0 (τ X1)
           grind)
        | exact resolve b3e33 b3e12349
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e33
      have b3e14151 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e14146 X0 X1
           have i₂ := b3e20 X1 X0
           grind)
        | exact superpose b3e20 b3e14146
        | (have j0 := b3e14146 X0 X1
           grind)
        | exact resolve b3e14146 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e14146
      have b3e18288 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e14 (σ X0) X1
           have i₂ := b3e92 X0 X0
           grind)
        | exact superpose b3e92 b3e14
        | (have j0 := b3e14 (σ X0) X1
           have j1 := b3e92 X0 X0
           grind)
        | exact resolve b3e14 b3e92
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e18333 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op (σ X1) (M.op (σ X1) X2)) ∨ (σ X0) = (σ (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e204 (σ X1) X2 (σ X0)
           have i₂ := b3e92 X0 X1
           grind)
        | exact superpose b3e92 b3e204
        | (have j1 := b3e92 X0 X1
           grind)
        | exact resolve b3e204 b3e92
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e92
      have b3e40313 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e103 X0 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e103
        | (have j0 := b3e103 X1 (σ X0)
           grind)
        | exact resolve b3e103 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e103
      have b3e40383 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e40313 X0 X1
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e40313
        | (have j0 := b3e40313 X0 X1
           grind)
        | exact resolve b3e40313 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e40313
      have b3e42047 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b3e1368 X0
           have i₂ := b3e40383 X0 X0
           grind)
        | exact superpose b3e40383 b3e1368
        | (have j0 := b3e1368 X0
           have j1 := b3e40383 X0 X0
           grind)
        | (have r₁ := b3e1368 x
           have r₂ := b3e40383 x x
           grind)
        | exact resolve b3e1368 b3e40383
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e40383
      have b3e42089 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b3e42047 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e42047
      have b3e85216 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e1371 x y
           grind)
        | exact superpose b3e1371 b3e16
        | (have j1 := b3e1371 x y
           grind)
        | exact resolve b3e16 b3e1371
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e85452 : y = (k y x) := by
        first
        | (have j1 := b3e14027 x y
           grind)
        | (have r₁ := b3e85216
           have r₂ := b3e14027 x y
           grind)
        | exact resolve b3e85216 b3e14027
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e14027 b3e85216
      have b3e89095 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e12349 x y
           have i₂ := b3e85452
           grind)
        | exact superpose b3e85452 b3e12349
        | (have j0 := b3e12349 x y
           grind)
        | exact resolve b3e12349 b3e85452
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e156077 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k X1 X1)
           have i₂ := b3e1290 X0 X1
           grind)
        | (have i₁ := b3e11 X0
           have i₂ := b3e1290 X0 X1
           grind)
        | exact superpose b3e1290 b3e11
        | (have j1 := b3e1290 X0 X1
           grind)
        | exact resolve b3e11 b3e1290
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1290
      have b3e156135 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e156077 X0 X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e156077
        | (have j0 := b3e156077 X0 X1
           grind)
        | exact resolve b3e156077 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e156077
      have b3e294722 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
        intro X0
        first
        | (have j0 := b3e12170 (τ X0) X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e12170
      have b3e294723 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b3e294722 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e294722
        | (have j0 := b3e294722 X0
           grind)
        | exact resolve b3e294722 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e294722
      have b3e298172 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b3e294723 X0
           have i₂ := b3e36 X0 X0
           grind)
        | exact superpose b3e36 b3e294723
        | (have j0 := b3e294723 X0
           have j1 := b3e36 X0 X0
           grind)
        | (have r₁ := b3e294723 X0
           have r₂ := b3e36 X0 X0
           grind)
        | exact resolve b3e294723 b3e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e36
      have b3e298188 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
        intro X0
        first
        | (have j0 := b3e298172 X0
           have j1 := b3e294723 X0
           grind)
        | (have r₁ := b3e298172 X0
           have r₂ := b3e294723 X0
           grind)
        | exact resolve b3e298172 b3e294723
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e294723 b3e298172
      have b3e300475 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b3e298188 (σ X0)
           have i₂ := b3e42089 X0
           grind)
        | exact superpose b3e42089 b3e298188
        | (have j0 := b3e298188 (σ X0)
           have j1 := b3e42089 X0
           grind)
        | (have r₁ := b3e298188 (σ X0)
           have r₂ := b3e42089 X0
           grind)
        | exact resolve b3e298188 b3e42089
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e42089 b3e298188
      have b3e300482 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b3e300475 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e300475
      have b3e300484 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b3e300482 X0
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e300482
        | (have j0 := b3e300482 X0
           grind)
        | exact resolve b3e300482 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e300482
      have b3e305012 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e300484 X1
           have i₂ := b3e12349 X0 X1
           grind)
        | (have i₁ := b3e300484 X0
           have i₂ := b3e12349 (M.op X0 X0) X1
           grind)
        | exact superpose b3e12349 b3e300484
        | (have j1 := b3e12349 X0 X1
           grind)
        | exact resolve b3e300484 b3e12349
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e300484
      have b3e356383 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e14151 X1 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e14151
        | (have j0 := b3e14151 X1 (σ X0)
           grind)
        | exact resolve b3e14151 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e14151
      have b3e356422 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e356383 X0 X1
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e356383
        | (have j0 := b3e356383 X0 X1
           grind)
        | exact resolve b3e356383 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e356383
      have b3e356425 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e356422 X0 X1
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e356422
        | (have j0 := b3e356422 X0 X1
           grind)
        | exact resolve b3e356422 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e356422
      have b3e424777 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b3e1368 X0
           have i₂ := b3e356425 X0 X0
           grind)
        | exact superpose b3e356425 b3e1368
        | (have j0 := b3e1368 X0
           have j1 := b3e356425 X0 X0
           grind)
        | (have r₁ := b3e1368 x
           have r₂ := b3e356425 x x
           grind)
        | exact resolve b3e1368 b3e356425
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e356425
      have b3e424811 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b3e424777 X0
           have j1 := b3e1368 X0
           grind)
        | (have r₁ := b3e424777 X0
           have r₂ := b3e1368 X0
           grind)
        | exact resolve b3e424777 b3e1368
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1368 b3e424777
      have b3e473666 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e156135 x y
           grind)
        | exact superpose b3e156135 b3e16
        | (have j1 := b3e156135 x y
           grind)
        | exact resolve b3e16 b3e156135
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e156135
      have b3e473670 : x = (k y y) ∨ (σ x) = (σ y) := by
        first
        | (have j1 := b3e305012 x y
           grind)
        | (have r₁ := b3e473666
           have r₂ := b3e305012 (M.op x y) (k y x)
           grind)
        | (have r₁ := b3e473666
           have r₂ := b3e305012 (k y x) (M.op x y)
           grind)
        | (have r₁ := b3e473666
           have r₂ := b3e305012 x y
           grind)
        | exact resolve b3e473666 b3e305012
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e305012 b3e473666
      have b3e500105 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b3e18288 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e18288
      have b3e500106 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b3e500105 X0 X1
           have j1 := b3e1291 X1 X0
           grind)
        | (have r₁ := b3e500105 (k X1 X1) X0
           have r₂ := b3e1291 X0 X1
           grind)
        | (have r₁ := b3e500105 X0 (σ (k X1 X1))
           have r₂ := b3e1291 (σ X0) X1
           grind)
        | (have r₁ := b3e500105 X1 X0
           have r₂ := b3e1291 X0 X1
           grind)
        | exact resolve b3e500105 b3e1291
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1291 b3e500105
      have b3e500126 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e20 X1 (τ X1)
           have i₂ := b3e500106 (τ X1) X0
           grind)
        | (have i₁ := b3e20 X0 X1
           have i₂ := b3e500106 X0 (σ (k (τ X0) X1))
           grind)
        | exact superpose b3e500106 b3e20
        | (have j1 := b3e500106 (τ X1) X0
           grind)
        | exact resolve b3e20 b3e500106
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20
      have b3e500127 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k X1 X1)
           have i₂ := b3e500106 X1 X0
           grind)
        | (have i₁ := b3e11 X0
           have i₂ := b3e500106 X0 (σ X0)
           grind)
        | exact superpose b3e500106 b3e11
        | (have j1 := b3e500106 X1 X0
           grind)
        | exact resolve b3e11 b3e500106
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e500106
      have b3e500144 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e500126 X0 X1
           have i₂ := b3e12 X1
           grind)
        | exact superpose b3e12 b3e500126
        | (have j0 := b3e500126 X0 X1
           grind)
        | exact resolve b3e500126 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e500126
      have b3e500152 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e500144 X0 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e500144
        | (have j0 := b3e500144 X0 X1
           grind)
        | exact resolve b3e500144 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e500144
      have b3e502393 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X0)) = (k X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e500127 (σ X0) X1
           grind)
        | exact superpose b3e500127 b3e15
        | (have j1 := b3e500127 (σ X0) X1
           grind)
        | exact resolve b3e15 b3e500127
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e500127
      have b3e502398 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e502393 X0 X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e502393
        | (have j0 := b3e502393 X0 X1
           grind)
        | exact resolve b3e502393 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e502393
      have b3e502833 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e502398 x y
           grind)
        | exact superpose b3e502398 b3e16
        | (have j1 := b3e502398 x y
           grind)
        | exact resolve b3e16 b3e502398
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e502398
      have b3e502937 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
        first
        | (have i₁ := b3e502833
           have i₂ := b3e85452
           grind)
        | exact superpose b3e85452 b3e502833
        | exact resolve b3e502833 b3e85452
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e85452 b3e502833
      have b3e502972 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e502937
           have i₂ := b3e89095
           grind)
        | exact superpose b3e89095 b3e502937
        | (have r₁ := b3e502937
           have r₂ := b3e89095
           grind)
        | exact resolve b3e502937 b3e89095
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e89095
      have b3e502973 : x = (k y y) ∨ x = (M.op y y) := by grind
      clear b3e502972
      have b3e503043 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e14 y y
           have i₂ := b3e502973
           grind)
        | exact superpose b3e502973 b3e14
        | (have j0 := b3e14 y x
           grind)
        | exact resolve b3e14 b3e502973
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e503060 : x = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e500152 y y
           have i₂ := b3e502973
           grind)
        | exact superpose b3e502973 b3e500152
        | exact resolve b3e500152 b3e502973
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e500152 b3e502973
      have b3e503065 : x = (M.op y y) ∨ x = y := by grind
      clear b3e503060
      have b3e503073 : y = (M.op y y) ∨ x = (M.op y y) := by grind
      clear b3e503043
      have b3e504197 : x ≠ y ∨ x = (M.op y y) := by grind
      clear b3e503073
      have b3e504211 : x = (M.op y y) := by
        first
        | (have r₁ := b3e504197
           have r₂ := b3e503065
           grind)
        | exact resolve b3e504197 b3e503065
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e503065 b3e504197
      have b3e504301 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b3e424811 y
           have i₂ := b3e504211
           grind)
        | exact superpose b3e504211 b3e424811
        | (have j0 := b3e424811 y
           grind)
        | exact resolve b3e424811 b3e504211
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e424811
      have b3e504361 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b3e204 y X0 y
           have i₂ := b3e504211
           grind)
        | exact superpose b3e504211 b3e204
        | exact resolve b3e204 b3e504211
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e204
      have b3e504448 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e682 X0 X1 y y
           have i₂ := b3e504211
           grind)
        | exact superpose b3e504211 b3e682
        | exact resolve b3e682 b3e504211
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e682
      have b3e504516 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e965 X0 X1 X2 y y
           have i₂ := b3e504211
           grind)
        | exact superpose b3e504211 b3e965
        | exact resolve b3e965 b3e504211
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e965
      have b3e504540 : ∀ X0 : G, x = (k x y) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b3e5758 y x y
           have i₂ := b3e504211
           grind)
        | exact superpose b3e504211 b3e5758
        | (have j0 := b3e5758 y X0 x
           grind)
        | exact resolve b3e5758 b3e504211
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e5758
      have b3e504839 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b3e504361 x
           have i₂ := b3e504448 y x
           grind)
        | exact superpose b3e504448 b3e504361
        | exact resolve b3e504361 b3e504448
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e504361
      have b3e507897 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) X2) = (M.op x X2) ∨ (k X0 X1) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e504516 (σ X1) (σ X0) X2
           have i₂ := b3e1371 X1 X0
           grind)
        | exact superpose b3e1371 b3e504516
        | (have j1 := b3e1371 X1 X0
           grind)
        | exact resolve b3e504516 b3e1371
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1371 b3e504516
      have b3e520467 : ∀ X0 : G, (σ x) = (σ (M.op y x)) ∨ y = (M.op x x) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b3e12349 y x
           have i₂ := b3e504540 X0
           grind)
        | exact superpose b3e504540 b3e12349
        | (have j0 := b3e12349 y x
           have j1 := b3e504540 X0
           grind)
        | exact resolve b3e12349 b3e504540
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e504540
      have b3e520567 : ∀ X0 : G, (σ x) = (σ (M.op y x)) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have j0 := b3e520467 X0
           grind)
        | (have r₁ := b3e520467 X0
           have r₂ := b3e17
           grind)
        | exact resolve b3e520467 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e520467
      have b3e520589 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b3e520567 X0
           have i₂ := b3e504839
           grind)
        | exact superpose b3e504839 b3e520567
        | (have j0 := b3e520567 X0
           grind)
        | exact resolve b3e520567 b3e504839
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e520567
      have b3e548048 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ x = (k y y) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b3e502937
           have i₂ := b3e520589 X0
           grind)
        | exact superpose b3e520589 b3e502937
        | (have j1 := b3e520589 X0
           grind)
        | exact resolve b3e502937 b3e520589
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e502937 b3e520589
      have b3e548084 : ∀ X0 : G, x = (k y y) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have j0 := b3e548048 X0
           grind)
        | (have r₁ := b3e548048 X0
           have r₂ := b3e473670
           grind)
        | exact resolve b3e548048 b3e473670
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e473670 b3e548048
      have b3e548261 : x ≠ (M.op y y) ∨ x = (k y y) := by grind
      clear b3e548084
      have b3e548263 : x = (k y y) := by
        first
        | (have r₁ := b3e548261
           have r₂ := b3e504211
           grind)
        | exact resolve b3e548261 b3e504211
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e548261
      have b3e548407 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ x) = (σ y) := by
        intro X0
        first
        | (have i₁ := b3e18333 y y x
           have i₂ := b3e548263
           grind)
        | exact superpose b3e548263 b3e18333
        | exact resolve b3e18333 b3e548263
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e18333
      have b3e548437 : (M.op (σ y) (σ x)) = (M.op x (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b3e548407 x
           have i₂ := b3e504448 (σ y) x
           grind)
        | exact superpose b3e504448 b3e548407
        | exact resolve b3e548407 b3e504448
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e504448 b3e548407
      have b3e548445 : (σ (k x y)) = (M.op x (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b3e548437
           have i₂ := b3e257
           grind)
        | exact superpose b3e257 b3e548437
        | exact resolve b3e548437 b3e257
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e257 b3e548437
      have b3e549077 : (σ (M.op y x)) = (M.op x (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b3e12349 y x
           have i₂ := b3e548445
           grind)
        | exact superpose b3e548445 b3e12349
        | (have j0 := b3e12349 y x
           grind)
        | exact resolve b3e12349 b3e548445
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e12349 b3e548445
      have b3e549089 : (σ (M.op y x)) = (M.op x (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have r₁ := b3e549077
           have r₂ := b3e17
           grind)
        | exact resolve b3e549077 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e549077
      have b3e549099 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b3e549089
           have i₂ := b3e504839
           grind)
        | exact superpose b3e504839 b3e549089
        | exact resolve b3e549089 b3e504839
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e504839 b3e549089
      have b3e556668 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b3e507897 y y x
           have i₂ := b3e548263
           grind)
        | exact superpose b3e548263 b3e507897
        | exact resolve b3e507897 b3e548263
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e507897 b3e548263
      have b3e556895 : (σ (M.op x y)) ≠ (M.op x (σ y)) ∨ x = y := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e556668 (σ y)
           grind)
        | exact superpose b3e556668 b3e16
        | exact resolve b3e16 b3e556668
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e556668
      have b3e557863 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b3e556895
           have i₂ := b3e549099
           grind)
        | exact superpose b3e549099 b3e556895
        | (have r₁ := b3e556895
           have r₂ := b3e549099
           grind)
        | exact resolve b3e556895 b3e549099
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e549099 b3e556895
      have b3e557867 : (σ x) = (σ y) ∨ x = y := by grind
      clear b3e557863
      have b3e557899 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b3e11 y
           have i₂ := b3e557867
           grind)
        | exact superpose b3e557867 b3e11
        | exact resolve b3e11 b3e557867
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e557867
      have b3e557986 : x = y ∨ x = y := by
        first
        | (have i₁ := b3e557899
           have i₂ := b3e11 x
           grind)
        | exact superpose b3e11 b3e557899
        | exact resolve b3e557899 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e557899
      have b3e557987 : x = y := by grind
      clear b3e557986
      have b3e558060 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e557987
           grind)
        | exact superpose b3e557987 b3e16
        | exact resolve b3e16 b3e557987
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e558206 : x = (M.op x x) := by
        first
        | (have i₁ := b3e504211
           have i₂ := b3e557987
           grind)
        | exact superpose b3e557987 b3e504211
        | exact resolve b3e504211 b3e557987
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e504211
      have b3e558213 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b3e504301
           have i₂ := b3e557987
           grind)
        | exact superpose b3e557987 b3e504301
        | exact resolve b3e504301 b3e557987
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e504301 b3e557987
      have b3e558317 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b3e558213
      have b3e558453 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b3e558060
           have i₂ := b3e558206
           grind)
        | exact superpose b3e558206 b3e558060
        | exact resolve b3e558060 b3e558206
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e558060 b3e558206
      have b3e558524 : False := by grind
      exact b3e558524

/-- `Equation4411`: `x ◇ (x ◇ y) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pxy_Equation4411 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4411 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4411.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op a b :=
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
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
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
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
      have b1e24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X2 (M.op X2 X0) X3
           have i₂ := b1e10 X2 X0 X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e26 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
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
      have b1e27 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op X0 x)) := by
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
      have b1e28 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X3 X2 (M.op X2 X0)
           have i₂ := b1e10 X2 X0 X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 (M.op X2 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e24 X0 X1 X2 X3
           have i₂ := b1e28 X2 X0 X3 X2
           grind)
        | exact superpose b1e28 b1e24
        | exact resolve b1e24 b1e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e24
      have b1e35 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 x X1
           have i₂ := b1e27 X0
           grind)
        | exact superpose b1e27 b1e10
        | exact resolve b1e10 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e37 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) X0) = (M.op X0 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 (M.op X0 x) X1
           have i₂ := b1e27 X0
           grind)
        | exact superpose b1e27 b1e10
        | exact resolve b1e10 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e39 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e37 X0 X1
           have i₂ := b1e28 X0 x X1 X0
           grind)
        | exact superpose b1e28 b1e37
        | exact resolve b1e37 b1e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e37
      have b1e42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b1e44 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y x) X0) := by
        intro X0
        first
        | (have i₁ := b1e35 X0 (M.op x x)
           have i₂ := b1e27 x
           grind)
        | exact superpose b1e27 b1e35
        | exact resolve b1e35 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e54 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op (M.op x X0) (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b1e27 (M.op x X0)
           have i₂ := b1e35 x X0
           grind)
        | exact superpose b1e35 b1e27
        | exact resolve b1e27 b1e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e55 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op y (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b1e54 X0
           have i₂ := b1e35 (M.op y x) X0
           grind)
        | exact superpose b1e35 b1e54
        | exact resolve b1e54 b1e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35 b1e54
      have b1e62 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b1e55 X0
           have i₂ := b1e27 y
           grind)
        | exact superpose b1e27 b1e55
        | exact resolve b1e55 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e55
      have b1e68 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e22 X0 X1
           have i₂ := b1e14 (τ X0) X1
           grind)
        | exact superpose b1e14 b1e22
        | (have j1 := b1e14 (τ X0) X1
           grind)
        | exact resolve b1e22 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e71 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
      have b1e96 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b1e117 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) x)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e26 X0 X1 (M.op (M.op X0 X1) x) X2
           have i₂ := b1e27 (M.op X0 X1)
           grind)
        | exact superpose b1e27 b1e26
        | exact resolve b1e26 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e119 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e26 X0 X1 X2 (M.op X0 x)
           have i₂ := b1e27 X0
           grind)
        | exact superpose b1e27 b1e26
        | exact resolve b1e26 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e145 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e44 X1
           have i₂ := b1e26 y x X1 X0
           grind)
        | (have i₁ := b1e44 X1
           have i₂ := b1e26 y X0 X1 x
           grind)
        | exact superpose b1e26 b1e44
        | exact resolve b1e44 b1e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e26 b1e44
      have b1e161 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e119 X0 X1 X2
           have i₂ := b1e145 X0 X2
           grind)
        | exact superpose b1e145 b1e119
        | exact resolve b1e119 b1e145
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e119 b1e145
      have b1e162 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 X2) (M.op x (M.op x X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e117 X0 X1 X2
           have i₂ := b1e10 x X0 X1
           grind)
        | exact superpose b1e10 b1e117
        | exact resolve b1e117 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e117
      have b1e170 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y (M.op x (M.op x X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e162 X0 X1 x
           have i₂ := b1e161 X0 x (M.op x (M.op x X0))
           grind)
        | exact superpose b1e161 b1e162
        | exact resolve b1e162 b1e161
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e162
      have b1e171 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y y) := by
        intro X0 X1
        first
        | (have i₁ := b1e170 X0 X1
           have i₂ := b1e62 (M.op x X0)
           grind)
        | exact superpose b1e62 b1e170
        | exact resolve b1e170 b1e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e62 b1e170
      have b1e188 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 X1 x
           have i₂ := b1e161 X1 x X0
           grind)
        | exact superpose b1e161 b1e10
        | exact resolve b1e10 b1e161
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e193 : ∀ X0 X1 X2 : G, (M.op y X0) ≠ X0 ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e13 (M.op X1 X2) X0
           have i₂ := b1e161 X1 X2 X0
           grind)
        | exact superpose b1e161 b1e13
        | (have j0 := b1e13 y X0
           grind)
        | exact resolve b1e13 b1e161
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e278 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op X2 (M.op X2 (M.op (M.op X3 X4) X1))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e10 X2 (M.op (M.op X3 X4) X1) X0
           have i₂ := b1e28 X3 X4 X1 X0
           grind)
        | exact superpose b1e28 b1e10
        | exact resolve b1e10 b1e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28
      have b1e288 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op X2 (M.op y X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e278 X0 X1 X2 x x
           have i₂ := b1e39 X2 (M.op (M.op x x) X1)
           grind)
        | exact superpose b1e39 b1e278
        | exact resolve b1e278 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e278
      have b1e319 : ∀ X2 : G, (M.op y X2) = (M.op X2 (M.op y X2)) := by
        intro X2
        first
        | (have i₁ := b1e288 x x X2
           have i₂ := b1e161 x (M.op x x) X2
           grind)
        | exact superpose b1e161 b1e288
        | exact resolve b1e288 b1e161
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e288
      have b1e448 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op (M.op X2 X3) X0) ∨ (k X0 (M.op (M.op X2 X3) X0)) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e13 X0 (M.op (M.op X2 X3) X0)
           have i₂ := b1e32 X2 X3 X0 X1
           grind)
        | (have i₁ := b1e13 X2 (M.op X2 X3)
           have i₂ := b1e32 X0 X1 X2 X3
           grind)
        | exact superpose b1e32 b1e13
        | (have j0 := b1e13 X0 (M.op (M.op X2 X3) X0)
           grind)
        | (have r₁ := b1e13 X2 (M.op X2 (M.op (M.op X0 X1) X2))
           have r₂ := b1e32 X0 X1 X2 (M.op (M.op X0 X1) X2)
           grind)
        | exact resolve b1e13 b1e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e32
      have b1e502 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op y X0) ∨ (k X0 (M.op (M.op X2 X3) X0)) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e448 X0 X1 X2 X3
           have i₂ := b1e161 X2 X3 X0
           grind)
        | exact superpose b1e161 b1e448
        | (have j0 := b1e448 X0 X1 X2 X3
           grind)
        | exact resolve b1e448 b1e161
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e448
      have b1e553 : ∀ X0 X2 X3 : G, (k X0 (M.op (M.op X2 X3) X0)) = X0 := by
        intro X0 X2 X3
        first
        | (have j0 := b1e502 X0 x X2 X3
           grind)
        | (have r₁ := b1e502 X0 x X2 X3
           have r₂ := b1e188 X0 x
           grind)
        | exact resolve b1e502 b1e188
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e502
      have b1e591 : ∀ X0 : G, (k X0 (M.op y X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b1e553 X0 x x
           have i₂ := b1e161 x x X0
           grind)
        | exact superpose b1e161 b1e553
        | exact resolve b1e553 b1e161
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e553
      have b1e676 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op y y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e591 (M.op X0 X1)
           have i₂ := b1e171 X0 X1
           grind)
        | exact superpose b1e171 b1e591
        | exact resolve b1e591 b1e171
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e682 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op y (τ X0)))) := by
        intro X0
        first
        | (have i₁ := b1e22 X0 (M.op y (τ X0))
           have i₂ := b1e591 (τ X0)
           grind)
        | exact superpose b1e591 b1e22
        | exact resolve b1e22 b1e591
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22
      have b1e683 : ∀ X0 : G, (k X0 (σ (M.op y (τ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e682 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e682
        | exact resolve b1e682 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e682
      have b1e1204 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b1e188 x y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e188
        | exact resolve b1e188 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1273 : y = (M.op y x) := by
        first
        | (have i₁ := b1e1204
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1204
        | exact resolve b1e1204 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1204
      have b1e2126 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e161 (σ X0) (σ X1) X2
           have i₂ := b1e42 X0 X1
           grind)
        | exact superpose b1e42 b1e161
        | (have j1 := b1e42 X0 X1
           grind)
        | exact resolve b1e161 b1e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e2127 : ∀ X0 X1 : G, (M.op y y) = (M.op y (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e171 (σ X0) (σ X1)
           have i₂ := b1e42 X0 X1
           grind)
        | exact superpose b1e42 b1e171
        | (have j1 := b1e42 X0 X1
           grind)
        | exact resolve b1e171 b1e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e2129 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b1e42 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e42
      have b1e2167 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e71 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e71
        | exact resolve b1e71 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e2172 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e71 X0 X1
           have i₂ := b1e14 X0 (σ X1)
           grind)
        | exact superpose b1e14 b1e71
        | (have j1 := b1e14 X0 (σ X1)
           grind)
        | exact resolve b1e71 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e2322 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e96 X0 X1
           have i₂ := b1e14 (σ X0) X1
           grind)
        | exact superpose b1e14 b1e96
        | (have j1 := b1e14 (σ X0) X1
           grind)
        | exact resolve b1e96 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e8093 : ∀ X0 : G, (σ X0) ≠ (σ (M.op y X0)) ∨ (σ (M.op y X0)) = (M.op (σ X0) (σ (M.op y X0))) := by
        intro X0
        first
        | (have i₁ := b1e2129 X0 (M.op y X0)
           have i₂ := b1e591 X0
           grind)
        | exact superpose b1e591 b1e2129
        | (have j0 := b1e2129 X0 (M.op y X0)
           grind)
        | exact resolve b1e2129 b1e591
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e591
      have b1e8108 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e2129 x y
           have i₂ := b1e21
           grind)
        | exact superpose b1e21 b1e2129
        | (have j0 := b1e2129 x y
           grind)
        | exact resolve b1e2129 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e8113 : (σ x) ≠ (σ y) := by
        first
        | (have r₁ := b1e8108
           have r₂ := b1e18
           grind)
        | exact resolve b1e8108 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e8108
      have b1e8127 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e68 (σ X0) X1
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e68
        | exact resolve b1e68 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e8137 : ∀ X0 : G, (σ (M.op y (τ X0))) = (k X0 (σ (M.op (τ X0) x))) ∨ (M.op y (τ X0)) = (M.op (τ X0) x) := by
        intro X0
        first
        | (have i₁ := b1e68 X0 (M.op (τ X0) x)
           have i₂ := b1e27 (τ X0)
           grind)
        | exact superpose b1e27 b1e68
        | exact resolve b1e68 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27 b1e68
      have b1e8174 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e8127 X0 X1
           have i₂ := b1e15 X0 X1
           grind)
        | exact superpose b1e15 b1e8127
        | (have j0 := b1e8127 X0 X1
           grind)
        | exact resolve b1e8127 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e8127
      have b1e15010 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e2126 x y X0
           have i₂ := b1e21
           grind)
        | exact superpose b1e21 b1e2126
        | (have j0 := b1e2126 x y x
           grind)
        | exact resolve b1e2126 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21 b1e2126
      have b1e15195 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b1e15010 X0
           grind)
        | (have r₁ := b1e15010 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e15010 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e15010
      have b1e15338 : ∀ X0 : G, (τ (M.op y X0)) = (k x (τ X0)) ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b1e2322 x X0
           have i₂ := b1e15195 X0
           grind)
        | exact superpose b1e15195 b1e2322
        | exact resolve b1e2322 b1e15195
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2322
      have b1e15340 : (σ y) ≠ (M.op y (σ y)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e15195 (σ y)
           grind)
        | exact superpose b1e15195 b1e18
        | exact resolve b1e18 b1e15195
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e15195
      have b1e15591 : ∀ X0 X1 : G, (M.op y y) = (M.op y (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e2127 (τ X0) (τ X1)
           have i₂ := b1e2167 X1 X0
           grind)
        | exact superpose b1e2167 b1e2127
        | (have j0 := b1e2127 (τ X0) (τ X1)
           grind)
        | exact resolve b1e2127 b1e2167
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2127 b1e2167
      have b1e15670 : ∀ X0 X1 : G, (M.op y y) = (M.op y (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e15591 X0 X1
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e15591
        | (have j0 := b1e15591 X0 X1
           grind)
        | exact resolve b1e15591 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e15591
      have b1e15677 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op y y) = (M.op y (k X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15670 X0 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e15670
        | (have j0 := b1e15670 X0 X1
           grind)
        | exact resolve b1e15670 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e15670
      have b1e15680 : ∀ X0 X1 : G, (M.op y y) = (M.op y (k X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e15677 X0 X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e15677
        | (have j0 := b1e15677 X0 X1
           grind)
        | exact resolve b1e15677 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e15677
      have b1e16571 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
        first
        | (have i₁ := b1e8093 (M.op y y)
           have i₂ := b1e319 y
           grind)
        | exact superpose b1e319 b1e8093
        | exact resolve b1e8093 b1e319
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e8093
      have b1e16573 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
      clear b1e16571
      have b1e18542 : ∀ X0 : G, (M.op y X0) = (M.op (σ (M.op y y)) X0) := by
        intro X0
        first
        | (have i₁ := b1e161 (σ (M.op y y)) (σ (M.op y y)) X0
           have i₂ := b1e16573
           grind)
        | exact superpose b1e16573 b1e161
        | exact resolve b1e161 b1e16573
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e161
      have b1e18544 : (M.op y y) = (M.op y (σ (M.op y y))) := by
        first
        | (have i₁ := b1e171 (σ (M.op y y)) (σ (M.op y y))
           have i₂ := b1e16573
           grind)
        | exact superpose b1e16573 b1e171
        | exact resolve b1e171 b1e16573
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e171
      have b1e18545 : (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op y (σ (M.op y y))) := by
        first
        | (have i₁ := b1e188 (σ (M.op y y)) (σ (M.op y y))
           have i₂ := b1e16573
           grind)
        | exact superpose b1e16573 b1e188
        | exact resolve b1e188 b1e16573
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e18558 : (σ (M.op y y)) = (M.op y (σ (M.op y y))) := by
        first
        | (have i₁ := b1e18545
           have i₂ := b1e16573
           grind)
        | exact superpose b1e16573 b1e18545
        | exact resolve b1e18545 b1e16573
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16573 b1e18545
      have b1e18595 : (M.op y y) = (σ (M.op y y)) := by
        first
        | (have i₁ := b1e18558
           have i₂ := b1e18544
           grind)
        | exact superpose b1e18544 b1e18558
        | exact resolve b1e18558 b1e18544
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18544 b1e18558
      have b1e18825 : (M.op y y) = (τ (M.op y y)) := by
        first
        | (have i₁ := b1e11 (M.op y y)
           have i₂ := b1e18595
           grind)
        | exact superpose b1e18595 b1e11
        | exact resolve b1e11 b1e18595
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e18834 : ∀ X0 : G, (τ (k X0 (M.op y y))) = (k (τ X0) (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b1e71 X0 (M.op y y)
           have i₂ := b1e18595
           grind)
        | exact superpose b1e18595 b1e71
        | exact resolve b1e71 b1e18595
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e71
      have b1e18839 : ∀ X0 : G, (τ (k (M.op y y) X0)) = (k (M.op y y) (τ X0)) := by
        intro X0
        first
        | (have i₁ := b1e96 (M.op y y) X0
           have i₂ := b1e18595
           grind)
        | exact superpose b1e18595 b1e96
        | exact resolve b1e96 b1e18595
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e96
      have b1e21325 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (k (τ (M.op X0 X1)) (M.op y y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e18834 (M.op X0 X1)
           have i₂ := b1e676 X0 X1
           grind)
        | exact superpose b1e676 b1e18834
        | exact resolve b1e18834 b1e676
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e676 b1e18834
      have b1e24543 : ∀ X0 : G, (M.op y X0) = (σ (k x (τ X0))) ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b1e12 (M.op y X0)
           have i₂ := b1e15338 X0
           grind)
        | exact superpose b1e15338 b1e12
        | (have j1 := b1e15338 X0
           grind)
        | exact resolve b1e12 b1e15338
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e15338
      have b1e24589 : ∀ X0 : G, (M.op y X0) = (k (σ x) X0) ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b1e24543 X0
           have i₂ := b1e23 X0 x
           grind)
        | exact superpose b1e23 b1e24543
        | (have j0 := b1e24543 X0
           grind)
        | exact resolve b1e24543 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23 b1e24543
      have b1e25203 : (τ (σ (M.op y (τ (M.op y y))))) = (k (M.op y y) (τ (σ (M.op (τ (M.op y y)) x)))) ∨ (M.op y (τ (M.op y y))) = (M.op (τ (M.op y y)) x) := by
        first
        | (have i₁ := b1e18839 (σ (M.op (τ (M.op y y)) x))
           have i₂ := b1e8137 (M.op y y)
           grind)
        | exact superpose b1e8137 b1e18839
        | (have j1 := b1e8137 (M.op y y)
           grind)
        | exact resolve b1e18839 b1e8137
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e8137
      have b1e25257 : (τ (σ (M.op y (τ (M.op y y))))) = (k (M.op y y) (M.op (τ (M.op y y)) x)) ∨ (M.op y (τ (M.op y y))) = (M.op (τ (M.op y y)) x) := by
        first
        | (have i₁ := b1e25203
           have i₂ := b1e11 (M.op (τ (M.op y y)) x)
           grind)
        | exact superpose b1e11 b1e25203
        | exact resolve b1e25203 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25203
      have b1e25289 : (k (M.op y y) (M.op (M.op y y) x)) = (τ (σ (M.op y (M.op y y)))) ∨ (M.op y (τ (M.op y y))) = (M.op (τ (M.op y y)) x) := by
        first
        | (have i₁ := b1e25257
           have i₂ := b1e18825
           grind)
        | exact superpose b1e18825 b1e25257
        | exact resolve b1e25257 b1e18825
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25257
      have b1e25309 : (M.op y (M.op y y)) = (k (M.op y y) (M.op (M.op y y) x)) ∨ (M.op y (τ (M.op y y))) = (M.op (τ (M.op y y)) x) := by
        first
        | (have i₁ := b1e25289
           have i₂ := b1e11 (M.op y (M.op y y))
           grind)
        | exact superpose b1e11 b1e25289
        | exact resolve b1e25289 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25289
      have b1e25322 : (M.op y (M.op y y)) = (k (M.op y y) (M.op x (M.op x y))) ∨ (M.op y (τ (M.op y y))) = (M.op (τ (M.op y y)) x) := by
        first
        | (have i₁ := b1e25309
           have i₂ := b1e10 x y y
           grind)
        | exact superpose b1e10 b1e25309
        | exact resolve b1e25309 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25309
      have b1e25328 : (M.op y (M.op y y)) = (k (M.op y y) (M.op x (M.op y x))) ∨ (M.op y (τ (M.op y y))) = (M.op (τ (M.op y y)) x) := by
        first
        | (have i₁ := b1e25322
           have i₂ := b1e39 x y
           grind)
        | exact superpose b1e39 b1e25322
        | exact resolve b1e25322 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25322
      have b1e25333 : (M.op y (M.op y y)) = (k (M.op y y) (M.op y x)) ∨ (M.op y (τ (M.op y y))) = (M.op (τ (M.op y y)) x) := by
        first
        | (have i₁ := b1e25328
           have i₂ := b1e319 x
           grind)
        | exact superpose b1e319 b1e25328
        | exact resolve b1e25328 b1e319
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25328
      have b1e25337 : (M.op y (M.op y y)) = (k (M.op y y) y) ∨ (M.op y (τ (M.op y y))) = (M.op (τ (M.op y y)) x) := by
        first
        | (have i₁ := b1e25333
           have i₂ := b1e1273
           grind)
        | exact superpose b1e1273 b1e25333
        | exact resolve b1e25333 b1e1273
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25333
      have b1e25341 : (M.op y y) = (k (M.op y y) y) ∨ (M.op y (τ (M.op y y))) = (M.op (τ (M.op y y)) x) := by
        first
        | (have i₁ := b1e25337
           have i₂ := b1e188 y y
           grind)
        | exact superpose b1e188 b1e25337
        | exact resolve b1e25337 b1e188
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25337
      have b1e25345 : (M.op y (M.op y y)) = (M.op (M.op y y) x) ∨ (M.op y y) = (k (M.op y y) y) := by
        first
        | (have i₁ := b1e25341
           have i₂ := b1e18825
           grind)
        | exact superpose b1e18825 b1e25341
        | exact resolve b1e25341 b1e18825
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25341
      have b1e25349 : (M.op x (M.op x y)) = (M.op y (M.op y y)) ∨ (M.op y y) = (k (M.op y y) y) := by
        first
        | (have i₁ := b1e25345
           have i₂ := b1e10 x y y
           grind)
        | exact superpose b1e10 b1e25345
        | exact resolve b1e25345 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25345
      have b1e25353 : (M.op x (M.op x y)) = (M.op y y) ∨ (M.op y y) = (k (M.op y y) y) := by
        first
        | (have i₁ := b1e25349
           have i₂ := b1e188 y y
           grind)
        | exact superpose b1e188 b1e25349
        | exact resolve b1e25349 b1e188
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e188 b1e25349
      have b1e25357 : (M.op y y) = (M.op x (M.op y x)) ∨ (M.op y y) = (k (M.op y y) y) := by
        first
        | (have i₁ := b1e25353
           have i₂ := b1e39 x y
           grind)
        | exact superpose b1e39 b1e25353
        | exact resolve b1e25353 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25353
      have b1e25361 : (M.op y x) = (M.op y y) ∨ (M.op y y) = (k (M.op y y) y) := by
        first
        | (have i₁ := b1e25357
           have i₂ := b1e319 x
           grind)
        | exact superpose b1e319 b1e25357
        | exact resolve b1e25357 b1e319
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25357
      have b1e25364 : y = (M.op y y) ∨ (M.op y y) = (k (M.op y y) y) := by
        first
        | (have i₁ := b1e25361
           have i₂ := b1e1273
           grind)
        | exact superpose b1e1273 b1e25361
        | exact resolve b1e25361 b1e1273
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25361
      have b1e25365 : (M.op y y) = (k (M.op y y) y) := by
        first
        | (have j1 := b1e193 y y y
           grind)
        | (have r₁ := b1e25364
           have r₂ := b1e193 y x x
           grind)
        | exact resolve b1e25364 b1e193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e193 b1e25364
      have b1e25367 : (τ (M.op y y)) = (k (M.op y y) (τ y)) := by
        first
        | (have i₁ := b1e18839 y
           have i₂ := b1e25365
           grind)
        | exact superpose b1e25365 b1e18839
        | exact resolve b1e18839 b1e25365
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18839
      have b1e25373 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
        first
        | (have i₁ := b1e2129 (M.op y y) y
           have i₂ := b1e25365
           grind)
        | exact superpose b1e25365 b1e2129
        | (have j0 := b1e2129 (M.op y y) y
           grind)
        | exact resolve b1e2129 b1e25365
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2129 b1e25365
      have b1e25394 : (σ y) ≠ (M.op y y) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
        first
        | (have i₁ := b1e25373
           have i₂ := b1e18595
           grind)
        | exact superpose b1e18595 b1e25373
        | exact resolve b1e25373 b1e18595
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25373
      have b1e25397 : (M.op y y) = (k (M.op y y) (τ y)) := by
        first
        | (have i₁ := b1e25367
           have i₂ := b1e18825
           grind)
        | exact superpose b1e18825 b1e25367
        | exact resolve b1e25367 b1e18825
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18825 b1e25367
      have b1e25401 : (σ y) = (M.op y (σ y)) ∨ (σ y) ≠ (M.op y y) := by
        first
        | (have i₁ := b1e25394
           have i₂ := b1e18542 (σ y)
           grind)
        | exact superpose b1e18542 b1e25394
        | exact resolve b1e25394 b1e18542
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18542 b1e25394
      have b1e25405 : (σ y) ≠ (M.op y y) := by
        first
        | (have r₁ := b1e25401
           have r₂ := b1e15340
           grind)
        | exact resolve b1e25401 b1e15340
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25401
      have b1e27214 : (σ x) = (M.op y (σ (M.op y (τ (σ x))))) ∨ (σ (M.op y (τ (σ x)))) = (M.op y (σ (M.op y (τ (σ x))))) := by
        first
        | (have i₁ := b1e683 (σ x)
           have i₂ := b1e24589 (σ (M.op y (τ (σ x))))
           grind)
        | exact superpose b1e24589 b1e683
        | (have j1 := b1e24589 (σ (M.op y (τ (σ x))))
           grind)
        | exact resolve b1e683 b1e24589
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e683 b1e24589
      have b1e27266 : (σ x) = (M.op y (σ (M.op y x))) ∨ (σ (M.op y (τ (σ x)))) = (M.op y (σ (M.op y (τ (σ x))))) := by
        first
        | (have i₁ := b1e27214
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e27214
        | exact resolve b1e27214 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27214
      have b1e27290 : (σ x) = (M.op y (σ y)) ∨ (σ (M.op y (τ (σ x)))) = (M.op y (σ (M.op y (τ (σ x))))) := by
        first
        | (have i₁ := b1e27266
           have i₂ := b1e1273
           grind)
        | exact superpose b1e1273 b1e27266
        | exact resolve b1e27266 b1e1273
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27266
      have b1e27309 : (σ (M.op y x)) = (M.op y (σ (M.op y x))) ∨ (σ x) = (M.op y (σ y)) := by
        first
        | (have i₁ := b1e27290
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e27290
        | exact resolve b1e27290 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27290
      have b1e27325 : (σ y) = (M.op y (σ y)) ∨ (σ x) = (M.op y (σ y)) := by
        first
        | (have i₁ := b1e27309
           have i₂ := b1e1273
           grind)
        | exact superpose b1e1273 b1e27309
        | exact resolve b1e27309 b1e1273
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27309
      have b1e27341 : (σ x) = (M.op y (σ y)) := by
        first
        | (have r₁ := b1e27325
           have r₂ := b1e15340
           grind)
        | exact resolve b1e27325 b1e15340
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e15340 b1e27325
      have b1e27913 : (τ (σ x)) = (k (τ y) y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b1e2172 y y
           have i₂ := b1e27341
           grind)
        | exact superpose b1e27341 b1e2172
        | exact resolve b1e2172 b1e27341
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2172 b1e27341
      have b1e27987 : (τ (σ x)) = (k (τ y) y) := by
        first
        | (have r₁ := b1e27913
           have r₂ := b1e8113
           grind)
        | exact resolve b1e27913 b1e8113
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27913
      have b1e28003 : x = (k (τ y) y) := by
        first
        | (have i₁ := b1e27987
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e27987
        | exact resolve b1e27987 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27987
      have b1e28444 : (M.op y x) = (M.op y y) ∨ y = (M.op (τ y) y) := by
        first
        | (have i₁ := b1e15680 (τ y) y
           have i₂ := b1e28003
           grind)
        | exact superpose b1e28003 b1e15680
        | (have j0 := b1e15680 (τ y) y
           grind)
        | exact resolve b1e15680 b1e28003
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e15680
      have b1e28446 : y = (M.op (τ y) y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e28444
           have i₂ := b1e1273
           grind)
        | exact superpose b1e1273 b1e28444
        | exact resolve b1e28444 b1e1273
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28444
      have b1e31134 : y ≠ y ∨ (τ y) = (k (τ y) y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e13 (τ y) y
           have i₂ := b1e28446
           grind)
        | exact superpose b1e28446 b1e13
        | (have j0 := b1e13 (τ y) y
           grind)
        | (have r₁ := b1e13 (τ y) y
           have r₂ := b1e28446
           grind)
        | (have r₁ := b1e13 y y
           have r₂ := b1e28446
           grind)
        | exact resolve b1e13 b1e28446
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28446
      have b1e31177 : (τ y) = (k (τ y) y) ∨ y = (M.op y y) := by grind
      clear b1e31134
      have b1e31196 : y = (M.op y y) ∨ x = (τ y) := by
        first
        | (have i₁ := b1e31177
           have i₂ := b1e28003
           grind)
        | exact superpose b1e28003 b1e31177
        | exact resolve b1e31177 b1e28003
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e31177
      have b1e31477 : (τ y) = (k (τ y) y) ∨ x = (τ y) := by
        first
        | (have i₁ := b1e21325 y y
           have i₂ := b1e31196
           grind)
        | exact superpose b1e31196 b1e21325
        | exact resolve b1e21325 b1e31196
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21325 b1e31196
      have b1e31489 : x = (τ y) ∨ x = (τ y) := by
        first
        | (have i₁ := b1e31477
           have i₂ := b1e28003
           grind)
        | exact superpose b1e28003 b1e31477
        | exact resolve b1e31477 b1e28003
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28003 b1e31477
      have b1e31490 : x = (τ y) := by grind
      clear b1e31489
      have b1e31729 : (M.op y y) = (k (M.op y y) x) := by
        first
        | (have i₁ := b1e25397
           have i₂ := b1e31490
           grind)
        | exact superpose b1e31490 b1e25397
        | exact resolve b1e25397 b1e31490
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25397 b1e31490
      have b1e34484 : (σ (M.op y y)) = (σ (M.op (M.op y y) x)) ∨ x = (M.op (M.op y y) x) := by
        first
        | (have i₁ := b1e8174 (M.op y y) x
           have i₂ := b1e31729
           grind)
        | exact superpose b1e31729 b1e8174
        | (have j0 := b1e8174 (M.op y y) x
           grind)
        | exact resolve b1e8174 b1e31729
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e8174 b1e31729
      have b1e34499 : (σ (M.op y y)) = (σ (M.op x (M.op x y))) ∨ x = (M.op (M.op y y) x) := by
        first
        | (have i₁ := b1e34484
           have i₂ := b1e10 x y y
           grind)
        | exact superpose b1e10 b1e34484
        | exact resolve b1e34484 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34484
      have b1e34518 : (σ (M.op y y)) = (σ (M.op x (M.op y x))) ∨ x = (M.op (M.op y y) x) := by
        first
        | (have i₁ := b1e34499
           have i₂ := b1e39 x y
           grind)
        | exact superpose b1e39 b1e34499
        | exact resolve b1e34499 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34499
      have b1e34531 : (σ (M.op y y)) = (σ (M.op y x)) ∨ x = (M.op (M.op y y) x) := by
        first
        | (have i₁ := b1e34518
           have i₂ := b1e319 x
           grind)
        | exact superpose b1e319 b1e34518
        | exact resolve b1e34518 b1e319
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34518
      have b1e34539 : (σ y) = (σ (M.op y y)) ∨ x = (M.op (M.op y y) x) := by
        first
        | (have i₁ := b1e34531
           have i₂ := b1e1273
           grind)
        | exact superpose b1e1273 b1e34531
        | exact resolve b1e34531 b1e1273
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34531
      have b1e34545 : (σ y) = (M.op y y) ∨ x = (M.op (M.op y y) x) := by
        first
        | (have i₁ := b1e34539
           have i₂ := b1e18595
           grind)
        | exact superpose b1e18595 b1e34539
        | exact resolve b1e34539 b1e18595
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18595 b1e34539
      have b1e34550 : x = (M.op (M.op y y) x) := by
        first
        | (have r₁ := b1e34545
           have r₂ := b1e25405
           grind)
        | exact resolve b1e34545 b1e25405
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25405 b1e34545
      have b1e34554 : x = (M.op x (M.op x y)) := by
        first
        | (have i₁ := b1e34550
           have i₂ := b1e10 x y y
           grind)
        | exact superpose b1e10 b1e34550
        | exact resolve b1e34550 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34550
      have b1e34558 : x = (M.op x (M.op y x)) := by
        first
        | (have i₁ := b1e34554
           have i₂ := b1e39 x y
           grind)
        | exact superpose b1e39 b1e34554
        | exact resolve b1e34554 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e39 b1e34554
      have b1e34562 : x = (M.op y x) := by
        first
        | (have i₁ := b1e34558
           have i₂ := b1e319 x
           grind)
        | exact superpose b1e319 b1e34558
        | exact resolve b1e34558 b1e319
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e319 b1e34558
      have b1e34564 : x = y := by
        first
        | (have i₁ := b1e34562
           have i₂ := b1e1273
           grind)
        | exact superpose b1e1273 b1e34562
        | exact resolve b1e34562 b1e1273
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1273 b1e34562
      have b1e34916 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e8113
           have i₂ := b1e34564
           grind)
        | exact superpose b1e34564 b1e8113
        | exact resolve b1e8113 b1e34564
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e8113 b1e34564
      have b1e34947 : False := by grind
      exact b1e34947
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
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
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
      have b2e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b2e31 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ x)) := by
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
      have b2e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X2 (M.op X2 X0) X3
           have i₂ := b2e10 X2 X0 X1
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
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
      have b2e35 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op X0 (σ x))) := by
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
      have b2e36 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X3 X2 (M.op X2 X0)
           have i₂ := b2e10 X2 X0 X1
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e40 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 (M.op X2 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e32 X0 X1 X2 X3
           have i₂ := b2e36 X2 X0 X3 X2
           grind)
        | exact superpose b2e36 b2e32
        | exact resolve b2e32 b2e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e32
      have b2e41 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ x)) := by
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
      have b2e45 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e11 (k (τ X0) X1)
           have i₂ := b2e25 X0 X1
           grind)
        | exact superpose b2e25 b2e11
        | exact resolve b2e11 b2e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e25
      have b2e48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b2e50 : x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b2e24
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e24
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e24 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e24
      have b2e53 : x = (M.op x y) := by
        first
        | (have r₁ := b2e50
           have r₂ := b2e17
           grind)
        | exact resolve b2e50 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50
      have b2e55 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e19
           have i₂ := b2e53
           grind)
        | exact superpose b2e53 b2e19
        | exact resolve b2e19 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19
      have b2e57 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b2e10 X0 x y
           have i₂ := b2e53
           grind)
        | exact superpose b2e53 b2e10
        | exact resolve b2e10 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e65 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e11 (k X0 (τ X1))
           have i₂ := b2e27 X1 X0
           grind)
        | exact superpose b2e27 b2e11
        | exact resolve b2e11 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27
      have b2e95 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op x X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e34 x X0 X1 y
           have i₂ := b2e53
           grind)
        | exact superpose b2e53 b2e34
        | exact resolve b2e34 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e129 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op (M.op X0 X2) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e34 X0 (M.op X0 (σ x)) X1 X2
           have i₂ := b2e35 X0
           grind)
        | exact superpose b2e35 b2e34
        | exact resolve b2e34 b2e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e131 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ x)) X1) X0) = (M.op X0 (M.op (σ y) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 (M.op X0 (σ x)) X1
           have i₂ := b2e35 X0
           grind)
        | exact superpose b2e35 b2e10
        | exact resolve b2e10 b2e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e136 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (σ y) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e131 X0 X1
           have i₂ := b2e36 X0 (σ x) X1 X0
           grind)
        | exact superpose b2e36 b2e131
        | exact resolve b2e131 b2e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e131
      have b2e145 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X1) = (M.op (M.op X0 X2) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e34 X0 (M.op X0 x) X1 X2
           have i₂ := b2e57 X0
           grind)
        | exact superpose b2e57 b2e34
        | exact resolve b2e34 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e146 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op X1 (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X1 X0 (M.op X0 x)
           have i₂ := b2e57 X0
           grind)
        | exact superpose b2e57 b2e10
        | exact resolve b2e10 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e147 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) X0) = (M.op X0 (M.op x X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 (M.op X0 x) X1
           have i₂ := b2e57 X0
           grind)
        | exact superpose b2e57 b2e10
        | exact resolve b2e10 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e151 : (σ y) = (M.op (M.op x (σ y)) (σ x)) := by
        first
        | (have i₁ := b2e41 (M.op (σ y) x)
           have i₂ := b2e57 (σ y)
           grind)
        | exact superpose b2e57 b2e41
        | exact resolve b2e41 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e41
      have b2e152 : (σ y) = (M.op (σ x) (M.op (σ x) x)) := by
        first
        | (have i₁ := b2e151
           have i₂ := b2e10 (σ x) x (σ y)
           grind)
        | exact superpose b2e10 b2e151
        | exact resolve b2e151 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e151
      have b2e155 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op x X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e147 X0 X1
           have i₂ := b2e36 X0 x X1 X0
           grind)
        | exact superpose b2e36 b2e147
        | exact resolve b2e147 b2e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e147
      have b2e156 : ∀ X0 X1 : G, (M.op x X1) = (M.op X1 (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e146 X0 X1
           have i₂ := b2e95 X0 X1
           grind)
        | exact superpose b2e95 b2e146
        | exact resolve b2e146 b2e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e146
      have b2e157 : ∀ X0 X1 X2 : G, (M.op x X1) = (M.op (M.op X0 X2) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e145 X0 X1 X2
           have i₂ := b2e95 X0 X1
           grind)
        | exact superpose b2e95 b2e145
        | exact resolve b2e145 b2e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e95 b2e145
      have b2e163 : (σ y) = (M.op x (σ x)) := by
        first
        | (have i₁ := b2e152
           have i₂ := b2e57 (σ x)
           grind)
        | exact superpose b2e57 b2e152
        | exact resolve b2e152 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e152
      have b2e203 : ∀ X0 X1 X2 : G, (M.op (σ y) X2) = (M.op (M.op (M.op X0 X1) (σ x)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e35 X2
           have i₂ := b2e36 X0 X1 (σ x) X2
           grind)
        | exact superpose b2e36 b2e35
        | exact resolve b2e35 b2e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e211 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op (M.op X3 X5) (M.op (M.op X3 X4) X2)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b2e34 X3 X4 (M.op (M.op X3 X4) X2) X5
           have i₂ := b2e36 X0 X1 X2 (M.op X3 X4)
           grind)
        | exact superpose b2e36 b2e34
        | exact resolve b2e34 b2e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e216 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op X2 (M.op X2 (M.op (M.op X3 X4) X1))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e10 X2 (M.op (M.op X3 X4) X1) X0
           have i₂ := b2e36 X3 X4 X1 X0
           grind)
        | exact superpose b2e36 b2e10
        | exact resolve b2e10 b2e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e36
      have b2e227 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op X2 (M.op (σ y) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e216 X0 X1 X2 x x
           have i₂ := b2e136 X2 (M.op (M.op x x) X1)
           grind)
        | exact superpose b2e136 b2e216
        | exact resolve b2e216 b2e136
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e216
      have b2e232 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op x (M.op (M.op X3 X4) X2)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e211 X0 X1 X2 X3 X4 x
           have i₂ := b2e157 X3 (M.op (M.op X3 X4) X2) x
           grind)
        | exact superpose b2e157 b2e211
        | exact resolve b2e211 b2e157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e211
      have b2e236 : ∀ X0 X1 X2 : G, (M.op (σ y) X2) = (M.op (M.op (σ y) (M.op X0 X1)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e203 X0 X1 X2
           have i₂ := b2e129 (M.op X0 X1) X2 (σ x)
           grind)
        | exact superpose b2e129 b2e203
        | exact resolve b2e203 b2e129
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e203
      have b2e262 : ∀ X0 X2 : G, (M.op (M.op (σ y) X0) X2) = (M.op X2 (M.op (σ y) X2)) := by
        intro X0 X2
        first
        | (have i₁ := b2e227 X0 x X2
           have i₂ := b2e129 X0 X2 (M.op X0 x)
           grind)
        | (have i₁ := b2e227 (σ y) x x
           have i₂ := b2e129 (M.op (σ y) x) x X2
           grind)
        | exact superpose b2e129 b2e227
        | exact resolve b2e227 b2e129
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e227
      have b2e264 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op x (M.op x X2)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e232 X0 X1 X2 X3 X4
           have i₂ := b2e157 X3 X2 X4
           grind)
        | exact superpose b2e157 b2e232
        | exact resolve b2e232 b2e157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e232
      have b2e267 : ∀ X2 : G, (M.op (σ y) X2) = (M.op (M.op (σ y) (σ y)) X2) := by
        intro X2
        first
        | (have i₁ := b2e236 x x X2
           have i₂ := b2e129 (σ y) X2 (M.op x x)
           grind)
        | (have i₁ := b2e236 x x x
           have i₂ := b2e129 (M.op x x) x X2
           grind)
        | exact superpose b2e129 b2e236
        | exact resolve b2e236 b2e129
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e129 b2e236
      have b2e283 : ∀ X2 : G, (M.op x X2) = (M.op X2 (M.op (σ y) X2)) := by
        intro X2
        first
        | (have i₁ := b2e262 x X2
           have i₂ := b2e157 (σ y) X2 x
           grind)
        | exact superpose b2e157 b2e262
        | exact resolve b2e262 b2e157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e262
      have b2e285 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op x x) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e264 X0 X1 X2 X3 X4
           have i₂ := b2e156 X2 x
           grind)
        | exact superpose b2e156 b2e264
        | exact resolve b2e264 b2e156
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e264
      have b2e287 : ∀ X2 : G, (M.op (σ y) X2) = (M.op x X2) := by
        intro X2
        first
        | (have i₁ := b2e267 X2
           have i₂ := b2e157 (σ y) X2 (σ y)
           grind)
        | exact superpose b2e157 b2e267
        | exact resolve b2e267 b2e157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e267
      have b2e300 : ∀ X3 X4 : G, (M.op x x) = (M.op x (M.op X3 X4)) := by
        intro X3 X4
        first
        | (have i₁ := b2e285 x x x X3 X4
           have i₂ := b2e157 (M.op x x) (M.op X3 X4) x
           grind)
        | exact superpose b2e157 b2e285
        | exact resolve b2e285 b2e157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e285
      have b2e376 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op (M.op X2 X3) X0) ∨ (k X0 (M.op (M.op X2 X3) X0)) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e13 X0 (M.op (M.op X2 X3) X0)
           have i₂ := b2e40 X2 X3 X0 X1
           grind)
        | (have i₁ := b2e13 X2 (M.op X2 X3)
           have i₂ := b2e40 X0 X1 X2 X3
           grind)
        | exact superpose b2e40 b2e13
        | (have j0 := b2e13 X0 (M.op (M.op X2 X3) X0)
           grind)
        | (have r₁ := b2e13 X2 (M.op X2 (M.op (M.op X0 X1) X2))
           have r₂ := b2e40 X0 X1 X2 (M.op (M.op X0 X1) X2)
           grind)
        | exact resolve b2e13 b2e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e40
      have b2e410 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op x X0) ∨ (k X0 (M.op (M.op X2 X3) X0)) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e376 X0 X1 X2 X3
           have i₂ := b2e157 X2 X0 X3
           grind)
        | exact superpose b2e157 b2e376
        | (have j0 := b2e376 X0 X1 X2 X3
           grind)
        | exact resolve b2e376 b2e157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e376
      have b2e451 : ∀ X0 X2 X3 : G, (k X0 (M.op (M.op X2 X3) X0)) = X0 := by
        intro X0 X2 X3
        first
        | (have j0 := b2e410 X0 x X2 X3
           grind)
        | (have r₁ := b2e410 x X0 X2 X3
           have r₂ := b2e156 X0 x
           grind)
        | exact resolve b2e410 b2e156
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e410
      have b2e481 : ∀ X0 : G, (k X0 (M.op x X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b2e451 X0 x x
           have i₂ := b2e157 x X0 x
           grind)
        | exact superpose b2e157 b2e451
        | exact resolve b2e451 b2e157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e451
      have b2e516 : (M.op x (σ x)) = (k (M.op x (σ x)) (M.op (σ y) x)) := by
        first
        | (have i₁ := b2e481 (M.op x (σ x))
           have i₂ := b2e35 x
           grind)
        | exact superpose b2e35 b2e481
        | exact resolve b2e481 b2e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e35
      have b2e517 : (M.op x x) = (k (M.op x x) (M.op x x)) := by
        first
        | (have i₁ := b2e481 (M.op x x)
           have i₂ := b2e57 x
           grind)
        | exact superpose b2e57 b2e481
        | exact resolve b2e481 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e57 b2e481
      have b2e524 : (M.op x (σ x)) = (k (M.op x (σ x)) (M.op x x)) := by
        first
        | (have i₁ := b2e516
           have i₂ := b2e287 x
           grind)
        | exact superpose b2e287 b2e516
        | exact resolve b2e516 b2e287
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e287 b2e516
      have b2e528 : (σ y) = (k (σ y) (M.op x x)) := by
        first
        | (have i₁ := b2e524
           have i₂ := b2e163
           grind)
        | exact superpose b2e163 b2e524
        | exact resolve b2e524 b2e163
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e524
      have b2e1769 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ X0) X2) X3) = (M.op (σ (k X0 X1)) X3) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e34 (σ X0) X2 X3 (σ X1)
           have i₂ := b2e48 X0 X1
           grind)
        | exact superpose b2e48 b2e34
        | (have j1 := b2e48 X0 X1
           grind)
        | exact resolve b2e34 b2e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34
      have b2e1778 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b2e48 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e48
      have b2e1785 : ∀ X0 X1 X3 : G, (M.op x X3) = (M.op (σ (k X0 X1)) X3) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b2e1769 X0 X1 x X3
           have i₂ := b2e157 (σ X0) X3 x
           grind)
        | exact superpose b2e157 b2e1769
        | (have j0 := b2e1769 X0 X1 x X3
           grind)
        | exact resolve b2e1769 b2e157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1769
      have b2e1909 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e45 X1 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e45
        | exact resolve b2e45 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e45
      have b2e1940 : (k y (τ (M.op x x))) = (τ (σ y)) := by
        first
        | (have i₁ := b2e65 y (M.op x x)
           have i₂ := b2e528
           grind)
        | exact superpose b2e528 b2e65
        | exact resolve b2e65 b2e528
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e65 b2e528
      have b2e1955 : y = (k y (τ (M.op x x))) := by
        first
        | (have i₁ := b2e1940
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e1940
        | exact resolve b2e1940 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1940
      have b2e9877 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
        first
        | (have i₁ := b2e1778 (M.op x x) (M.op x x)
           have i₂ := b2e517
           grind)
        | exact superpose b2e517 b2e1778
        | (have j0 := b2e1778 (M.op x x) (M.op x x)
           grind)
        | exact resolve b2e1778 b2e517
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e517 b2e1778
      have b2e9892 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by grind
      clear b2e9877
      have b2e12324 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (M.op x (σ (M.op x x)))) := by
        first
        | (have i₁ := b2e155 (σ (M.op x x)) (σ (M.op x x))
           have i₂ := b2e9892
           grind)
        | exact superpose b2e9892 b2e155
        | exact resolve b2e155 b2e9892
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e155
      have b2e12326 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x x)) X0) := by
        intro X0
        first
        | (have i₁ := b2e157 (σ (M.op x x)) X0 (σ (M.op x x))
           have i₂ := b2e9892
           grind)
        | exact superpose b2e9892 b2e157
        | exact resolve b2e157 b2e9892
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e157
      have b2e12333 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op x (M.op x (σ (M.op x x)))) := by
        first
        | (have i₁ := b2e12324
           have i₂ := b2e12326 (M.op x (σ (M.op x x)))
           grind)
        | exact superpose b2e12326 b2e12324
        | exact resolve b2e12324 b2e12326
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e12324 b2e12326
      have b2e12366 : (M.op x (M.op (σ y) x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
        first
        | (have i₁ := b2e12333
           have i₂ := b2e136 x (σ (M.op x x))
           grind)
        | exact superpose b2e136 b2e12333
        | exact resolve b2e12333 b2e136
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e136 b2e12333
      have b2e12385 : (M.op x (M.op (σ y) x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b2e12366
           have i₂ := b2e9892
           grind)
        | exact superpose b2e9892 b2e12366
        | exact resolve b2e12366 b2e9892
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e9892 b2e12366
      have b2e12397 : (M.op x x) = (σ (M.op x x)) := by
        first
        | (have i₁ := b2e12385
           have i₂ := b2e283 x
           grind)
        | (have i₁ := b2e12385
           have i₂ := b2e283 (M.op (σ y) x)
           grind)
        | exact superpose b2e283 b2e12385
        | exact resolve b2e12385 b2e283
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e12385
      have b2e13912 : (M.op x x) = (τ (M.op x x)) := by
        first
        | (have i₁ := b2e11 (M.op x x)
           have i₂ := b2e12397
           grind)
        | exact superpose b2e12397 b2e11
        | exact resolve b2e11 b2e12397
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e14829 : y = (k y (M.op x x)) := by
        first
        | (have i₁ := b2e1955
           have i₂ := b2e13912
           grind)
        | exact superpose b2e13912 b2e1955
        | exact resolve b2e1955 b2e13912
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1955 b2e13912
      have b2e17334 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op (σ (τ (k X0 X1))) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e1785 (τ X0) (τ X1) X2
           have i₂ := b2e1909 X1 X0
           grind)
        | exact superpose b2e1909 b2e1785
        | (have j0 := b2e1785 (τ X0) (τ X1) x
           grind)
        | exact resolve b2e1785 b2e1909
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1785 b2e1909
      have b2e17519 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e17334 X0 X1 X2
           have i₂ := b2e12 (k X0 X1)
           grind)
        | exact superpose b2e12 b2e17334
        | (have j0 := b2e17334 X0 X1 X2
           grind)
        | exact resolve b2e17334 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e17334
      have b2e17581 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op x X2) = (M.op (k X0 X1) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e17519 X0 X0 X2
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e17519
        | (have j0 := b2e17519 X0 X1 X2
           grind)
        | exact resolve b2e17519 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e17519
      have b2e17606 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op (k X0 X1) X2) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e17581 X0 X1 X2
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e17581
        | (have j0 := b2e17581 X0 X1 X2
           grind)
        | exact resolve b2e17581 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e17581
      have b2e20595 : ∀ X0 X1 : G, (M.op x (k X0 X1)) = (M.op x (M.op (σ y) (k X0 X1))) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e283 (k X0 X1)
           have i₂ := b2e17606 X0 X1 (M.op (σ y) (k X0 X1))
           grind)
        | exact superpose b2e17606 b2e283
        | (have j1 := b2e17606 X0 X1 x
           grind)
        | exact resolve b2e283 b2e17606
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e283 b2e17606
      have b2e20610 : ∀ X0 X1 : G, (M.op x x) = (M.op x (k X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e20595 X0 X1
           have i₂ := b2e300 (σ y) (k X0 X1)
           grind)
        | exact superpose b2e300 b2e20595
        | (have j0 := b2e20595 X0 X1
           grind)
        | exact resolve b2e20595 b2e300
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e300 b2e20595
      have b2e21337 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y (M.op x x)) := by
        first
        | (have i₁ := b2e20610 y (M.op x x)
           have i₂ := b2e14829
           grind)
        | exact superpose b2e14829 b2e20610
        | (have j0 := b2e20610 y (M.op x x)
           grind)
        | exact resolve b2e20610 b2e14829
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e14829 b2e20610
      have b2e21403 : (M.op x x) = (M.op y (M.op x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b2e21337
           have i₂ := b2e53
           grind)
        | exact superpose b2e53 b2e21337
        | exact resolve b2e21337 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21337
      have b2e21697 : (M.op x y) = (M.op y (M.op x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b2e156 (M.op x x) y
           have i₂ := b2e21403
           grind)
        | exact superpose b2e21403 b2e156
        | exact resolve b2e156 b2e21403
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e156
      have b2e21709 : x = (M.op y (M.op x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b2e21697
           have i₂ := b2e53
           grind)
        | exact superpose b2e53 b2e21697
        | exact resolve b2e21697 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e53 b2e21697
      have b2e21778 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b2e21403
           have i₂ := b2e21709
           grind)
        | exact superpose b2e21709 b2e21403
        | exact resolve b2e21403 b2e21709
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21403 b2e21709
      have b2e21823 : x = (M.op x x) := by grind
      clear b2e21778
      have b2e21982 : x = (σ x) := by
        first
        | (have i₁ := b2e12397
           have i₂ := b2e21823
           grind)
        | exact superpose b2e21823 b2e12397
        | exact resolve b2e12397 b2e21823
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e12397
      have b2e22252 : x ≠ (σ y) := by
        first
        | (have i₁ := b2e55
           have i₂ := b2e21982
           grind)
        | exact superpose b2e21982 b2e55
        | exact resolve b2e55 b2e21982
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e55
      have b2e22260 : (σ y) = (M.op x x) := by
        first
        | (have i₁ := b2e163
           have i₂ := b2e21982
           grind)
        | exact superpose b2e21982 b2e163
        | exact resolve b2e163 b2e21982
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e163 b2e21982
      have b2e22298 : x = (σ y) := by
        first
        | (have i₁ := b2e22260
           have i₂ := b2e21823
           grind)
        | exact superpose b2e21823 b2e22260
        | exact resolve b2e22260 b2e21823
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21823 b2e22260
      have b2e22309 : False := by grind
      exact b2e22309
    · have b3e14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x y) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b3e1041 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
      clear b3e34
      have b3e1068 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have r₁ := b3e1041
           have r₂ := b3e18
           grind)
        | exact resolve b3e1041 b3e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1041
      have b3e1071 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b3e1068
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e1068
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e1068 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1068
      have b3e1072 : y = (M.op x y) := by grind
      clear b3e1071
      have b3e1073 : False := by grind
      exact b3e1073

/-- `Equation4411`: `x ◇ (x ◇ y) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation4411 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4411 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4411.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
        intro X0 X1 X2
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op y x) := by grind
      have b0e18 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X2 X0 X3
           have i₂ := b0e10 X2 X0 X1
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X3 X2 (M.op X2 X0)
           have i₂ := b0e10 X2 X0 X1
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ y) X0) := by
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
      have b0e37 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op y X0) := by
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
      have b0e43 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op y X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 y X1
           have i₂ := b0e37 X0
           grind)
        | exact superpose b0e37 b0e10
        | exact resolve b0e10 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X1) X0) = (M.op X0 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 (M.op X0 y) X1
           have i₂ := b0e37 X0
           grind)
        | exact superpose b0e37 b0e10
        | exact resolve b0e10 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e47 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e45 X0 X1
           have i₂ := b0e34 X0 y X1 X0
           grind)
        | exact superpose b0e34 b0e45
        | exact resolve b0e45 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e58 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op X1 (M.op y X2))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 (M.op y X2) X0
           have i₂ := b0e43 X0 X2
           grind)
        | exact superpose b0e43 b0e10
        | exact resolve b0e10 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e67 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op y X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e58 X0 X1 x
           have i₂ := b0e47 X1 (M.op y x)
           grind)
        | exact superpose b0e47 b0e58
        | exact resolve b0e58 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e58
      have b0e69 : ∀ X1 : G, (M.op y X1) = (M.op X1 (M.op y X1)) := by
        intro X1
        first
        | (have i₁ := b0e67 x X1
           have i₂ := b0e43 X1 x
           grind)
        | exact superpose b0e43 b0e67
        | exact resolve b0e67 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67
      have b0e79 : y = (M.op x y) := by
        first
        | (have i₁ := b0e69 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e69
        | exact resolve b0e69 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e111 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e33 X0 X1 X2 (M.op y X0)
           have i₂ := b0e69 X0
           grind)
        | exact superpose b0e69 b0e33
        | exact resolve b0e33 b0e69
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e154 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e111 X0 X1 X2
           have i₂ := b0e43 X2 X0
           grind)
        | exact superpose b0e43 b0e111
        | exact resolve b0e111 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e111
      have b0e342 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (σ y)) X2) = (M.op (σ y) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e36 X2
           have i₂ := b0e34 X0 X1 (σ y) X2
           grind)
        | exact superpose b0e34 b0e36
        | exact resolve b0e36 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34 b0e36
      have b0e378 : ∀ X2 : G, (M.op y X2) = (M.op (σ y) X2) := by
        intro X2
        first
        | (have i₁ := b0e342 x x X2
           have i₂ := b0e154 (M.op x x) (σ y) X2
           grind)
        | exact superpose b0e154 b0e342
        | exact resolve b0e342 b0e154
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e154 b0e342
      have b0e457 : (σ y) = (M.op y (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e378 (σ x)
           grind)
        | exact superpose b0e378 b0e18
        | exact resolve b0e18 b0e378
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e378
      have b0e770 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e69 (σ x)
           have i₂ := b0e457
           grind)
        | exact superpose b0e457 b0e69
        | exact resolve b0e69 b0e457
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69 b0e457
      have b0e2119 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e770
           grind)
        | exact superpose b0e770 b0e16
        | exact resolve b0e16 b0e770
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e770
      have b0e2149 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e2119
           have i₂ := b0e79
           grind)
        | exact superpose b0e79 b0e2119
        | exact resolve b0e2119 b0e79
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79 b0e2119
      have b0e2150 : False := by grind
      exact b0e2150
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
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
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
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
      have b1e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op X1 X2)) = (M.op (M.op X1 X2) (M.op X0 (M.op X0 X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 (M.op X1 X2) X0 X3
           have i₂ := b1e10 X0 X1 X2
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
      have b1e30 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op y X0) := by
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
      have b1e31 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X3 X2 (M.op X2 X0)
           have i₂ := b1e10 X2 X0 X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e34 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X1 X2) ∨ (k X0 (M.op X1 X2)) = X0 := by
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
      have b1e40 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X1) X0) = (M.op X0 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 (M.op X0 y) X1
           have i₂ := b1e30 X0
           grind)
        | exact superpose b1e30 b1e10
        | exact resolve b1e10 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e42 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e40 X0 X1
           have i₂ := b1e31 X0 y X1 X0
           grind)
        | exact superpose b1e31 b1e40
        | exact resolve b1e40 b1e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e40
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
      have b1e53 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op X1 (M.op y X2))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 X1 (M.op y X2) X0
           have i₂ := b1e38 X0 X2
           grind)
        | exact superpose b1e38 b1e10
        | exact resolve b1e10 b1e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e56 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op y X0) X1)) = (M.op (M.op X1 X2) (M.op y X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (M.op y X0) X1 X2
           have i₂ := b1e38 (M.op (M.op y X0) X1) X0
           grind)
        | exact superpose b1e38 b1e10
        | exact resolve b1e10 b1e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e60 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op y X0)) = (M.op y (M.op y X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e56 X0 X1 X2
           have i₂ := b1e38 X1 X0
           grind)
        | exact superpose b1e38 b1e56
        | exact resolve b1e56 b1e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e56
      have b1e62 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op y X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e53 X0 X1 x
           have i₂ := b1e42 X1 (M.op y x)
           grind)
        | exact superpose b1e42 b1e53
        | exact resolve b1e53 b1e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e42 b1e53
      have b1e64 : ∀ X1 : G, (M.op y X1) = (M.op X1 (M.op y X1)) := by
        intro X1
        first
        | (have i₁ := b1e62 x X1
           have i₂ := b1e38 X1 x
           grind)
        | exact superpose b1e38 b1e62
        | exact resolve b1e62 b1e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e62
      have b1e71 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b1e101 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e29 X0 X1 (M.op (M.op X0 X1) y) X2
           have i₂ := b1e30 (M.op X0 X1)
           grind)
        | exact superpose b1e30 b1e29
        | exact resolve b1e29 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e106 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e29 X0 X1 X2 (M.op y X0)
           have i₂ := b1e64 X0
           grind)
        | exact superpose b1e64 b1e29
        | exact resolve b1e29 b1e64
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e134 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X2)) = (M.op (M.op X0 X1) (M.op y (M.op X0 X2))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e64 (M.op X0 X2)
           have i₂ := b1e29 X0 X2 (M.op y (M.op X0 X2)) X1
           grind)
        | (have i₁ := b1e64 (M.op X0 X2)
           have i₂ := b1e29 X0 X1 (M.op y (M.op X0 X2)) X2
           grind)
        | exact superpose b1e29 b1e64
        | exact resolve b1e64 b1e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e137 : ∀ X0 X2 : G, (M.op y (M.op y X0)) = (M.op y (M.op X0 X2)) := by
        intro X0 X2
        first
        | (have i₁ := b1e134 X0 x X2
           have i₂ := b1e60 (M.op X0 X2) X0 x
           grind)
        | exact superpose b1e60 b1e134
        | exact resolve b1e134 b1e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e60 b1e134
      have b1e147 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e106 X0 X1 X2
           have i₂ := b1e38 X2 X0
           grind)
        | exact superpose b1e38 b1e106
        | exact resolve b1e106 b1e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38 b1e106
      have b1e150 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 X2) (M.op y (M.op y X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e101 X0 X1 X2
           have i₂ := b1e10 y X0 X1
           grind)
        | exact superpose b1e10 b1e101
        | exact resolve b1e101 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e101
      have b1e160 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y (M.op y (M.op y X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e150 X0 X1 x
           have i₂ := b1e147 X0 x (M.op y (M.op y X0))
           grind)
        | exact superpose b1e147 b1e150
        | exact resolve b1e150 b1e147
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e150
      have b1e161 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y (M.op y y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e160 X0 X1
           have i₂ := b1e137 y (M.op y X0)
           grind)
        | (have i₁ := b1e160 X0 X1
           have i₂ := b1e137 (M.op y X0) x
           grind)
        | exact superpose b1e137 b1e160
        | exact resolve b1e160 b1e137
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e160
      have b1e162 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y y) := by
        intro X0 X1
        first
        | (have i₁ := b1e161 X0 X1
           have i₂ := b1e30 y
           grind)
        | exact superpose b1e30 b1e161
        | exact resolve b1e161 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e161
      have b1e218 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X2 X3) X4) X0) := by
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
      have b1e233 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e218 X0 X1 x x x
           have i₂ := b1e147 (M.op x x) x X0
           grind)
        | exact superpose b1e147 b1e218
        | exact resolve b1e218 b1e147
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e218
      have b1e1231 : ∀ X0 : G, (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have j0 := b1e34 X0 X0 (M.op X0 X0)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34
      have b1e1232 : ∀ X0 : G, (k X0 (M.op y X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b1e1231 X0
           have i₂ := b1e233 X0 X0
           grind)
        | exact superpose b1e233 b1e1231
        | exact resolve b1e1231 b1e233
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1231
      have b1e1330 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op y y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e1232 (M.op X0 X1)
           have i₂ := b1e162 X0 X1
           grind)
        | exact superpose b1e162 b1e1232
        | exact resolve b1e1232 b1e162
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e2033 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (σ X0) (M.op (σ X0) X2))) = (M.op (σ (k X0 X1)) (M.op X2 X3)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e28 (σ X0) X2 X3 (σ X1)
           have i₂ := b1e45 X0 X1
           grind)
        | exact superpose b1e45 b1e28
        | (have j1 := b1e45 X0 X1
           grind)
        | exact resolve b1e28 b1e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28
      have b1e2069 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b1e45 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e45
      have b1e2096 : ∀ X0 X1 X2 X3 : G, (M.op (σ (k X0 X1)) (M.op X2 X3)) = (M.op y (M.op (σ X0) (M.op (σ X0) X2))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e2033 X0 X1 X2 X3
           have i₂ := b1e147 X2 X3 (M.op (σ X0) (M.op (σ X0) X2))
           grind)
        | exact superpose b1e147 b1e2033
        | (have j0 := b1e2033 X0 X1 X2 X3
           grind)
        | exact resolve b1e2033 b1e147
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e147 b1e2033
      have b1e2116 : ∀ X0 X1 X2 X3 : G, (M.op (σ (k X0 X1)) (M.op X2 X3)) = (M.op y (M.op y (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e2096 X0 X1 X2 X3
           have i₂ := b1e137 (σ X0) (M.op (σ X0) X2)
           grind)
        | exact superpose b1e137 b1e2096
        | (have j0 := b1e2096 X0 X1 X2 X3
           grind)
        | exact resolve b1e2096 b1e137
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2096
      have b1e2124 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op y y)) = (M.op (σ (k X0 X1)) (M.op X2 X3)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e2116 X0 X1 X2 X3
           have i₂ := b1e137 y (σ X0)
           grind)
        | (have i₁ := b1e2116 X0 X1 X2 X3
           have i₂ := b1e137 (σ X0) X2
           grind)
        | exact superpose b1e137 b1e2116
        | (have j0 := b1e2116 X0 X1 X2 X3
           grind)
        | exact resolve b1e2116 b1e137
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e137 b1e2116
      have b1e2130 : ∀ X0 X1 X2 X3 : G, (M.op y y) = (M.op (σ (k X0 X1)) (M.op X2 X3)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e2124 X0 X1 X2 X3
           have i₂ := b1e162 y y
           grind)
        | exact superpose b1e162 b1e2124
        | (have j0 := b1e2124 X0 X1 X2 X3
           grind)
        | exact resolve b1e2124 b1e162
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2124
      have b1e2296 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op y (σ X0)))) := by
        intro X0
        first
        | (have i₁ := b1e71 X0 (M.op y (σ X0))
           have i₂ := b1e1232 (σ X0)
           grind)
        | exact superpose b1e1232 b1e71
        | exact resolve b1e71 b1e1232
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e71 b1e1232
      have b1e2308 : ∀ X0 : G, (k X0 (τ (M.op y (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e2296 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e2296
        | exact resolve b1e2296 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2296
      have b1e6444 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
        first
        | (have i₁ := b1e2069 (M.op y y)
           have i₂ := b1e1330 y y
           grind)
        | exact superpose b1e1330 b1e2069
        | (have j0 := b1e2069 (M.op y y)
           grind)
        | exact resolve b1e2069 b1e1330
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1330 b1e2069
      have b1e6449 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
      clear b1e6444
      have b1e6972 : (M.op y y) = (M.op y (σ (M.op y y))) := by
        first
        | (have i₁ := b1e162 (σ (M.op y y)) (σ (M.op y y))
           have i₂ := b1e6449
           grind)
        | exact superpose b1e6449 b1e162
        | exact resolve b1e162 b1e6449
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e6973 : (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op y (σ (M.op y y))) := by
        first
        | (have i₁ := b1e233 (σ (M.op y y)) (σ (M.op y y))
           have i₂ := b1e6449
           grind)
        | exact superpose b1e6449 b1e233
        | exact resolve b1e233 b1e6449
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e233
      have b1e6976 : (σ (M.op y y)) = (M.op y (σ (M.op y y))) := by
        first
        | (have i₁ := b1e6973
           have i₂ := b1e6449
           grind)
        | exact superpose b1e6449 b1e6973
        | exact resolve b1e6973 b1e6449
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6449 b1e6973
      have b1e7007 : (M.op y y) = (σ (M.op y y)) := by
        first
        | (have i₁ := b1e6976
           have i₂ := b1e6972
           grind)
        | exact superpose b1e6972 b1e6976
        | exact resolve b1e6976 b1e6972
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6972 b1e6976
      have b1e8405 : (M.op y y) = (τ (M.op y y)) := by
        first
        | (have i₁ := b1e11 (M.op y y)
           have i₂ := b1e7007
           grind)
        | exact superpose b1e7007 b1e11
        | exact resolve b1e11 b1e7007
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e12093 : ∀ X0 X1 : G, (M.op y y) = (M.op (σ x) (M.op X0 X1)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        intro X0 X1
        first
        | (have i₁ := b1e2130 x y X0 X1
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e2130
        | (have j0 := b1e2130 x y x x
           grind)
        | exact resolve b1e2130 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e2130
      have b1e12273 : ∀ X0 X1 : G, (M.op y y) = (M.op (σ x) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have j0 := b1e12093 X0 X1
           grind)
        | (have r₁ := b1e12093 X0 X1
           have r₂ := b1e18
           grind)
        | exact resolve b1e12093 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e12093
      have b1e12410 : (M.op y y) = (M.op y (σ x)) := by
        first
        | (have i₁ := b1e64 (σ x)
           have i₂ := b1e12273 y (σ x)
           grind)
        | exact superpose b1e12273 b1e64
        | exact resolve b1e64 b1e12273
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e64 b1e12273
      have b1e13247 : x = (k x (τ (M.op y y))) := by
        first
        | (have i₁ := b1e2308 x
           have i₂ := b1e12410
           grind)
        | exact superpose b1e12410 b1e2308
        | exact resolve b1e2308 b1e12410
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2308
      have b1e13302 : x = (k x (M.op y y)) := by
        first
        | (have i₁ := b1e13247
           have i₂ := b1e8405
           grind)
        | exact superpose b1e8405 b1e13247
        | exact resolve b1e13247 b1e8405
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e8405 b1e13247
      have b1e13380 : x = (M.op x (M.op y y)) ∨ (M.op y y) = (M.op (M.op y y) x) := by
        first
        | (have i₁ := b1e14 x (M.op y y)
           have i₂ := b1e13302
           grind)
        | exact superpose b1e13302 b1e14
        | (have j0 := b1e14 (M.op y y) x
           grind)
        | exact resolve b1e14 b1e13302
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13302
      have b1e13391 : (M.op y y) = (M.op x (M.op x y)) ∨ x = (M.op x (M.op y y)) := by
        first
        | (have i₁ := b1e13380
           have i₂ := b1e10 x y y
           grind)
        | exact superpose b1e10 b1e13380
        | exact resolve b1e13380 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13380
      have b1e13395 : (M.op y x) = (M.op y y) ∨ x = (M.op x (M.op y y)) := by
        first
        | (have i₁ := b1e13391
           have i₂ := b1e30 x
           grind)
        | exact superpose b1e30 b1e13391
        | exact resolve b1e13391 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30 b1e13391
      have b1e13399 : x = (M.op x (M.op y y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e13395
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e13395
        | exact resolve b1e13395 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13395
      have b1e15292 : (M.op y x) = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e162 x (M.op y y)
           have i₂ := b1e13399
           grind)
        | exact superpose b1e13399 b1e162
        | exact resolve b1e162 b1e13399
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e162 b1e13399
      have b1e15301 : y = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e15292
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e15292
        | exact resolve b1e15292 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e15292
      have b1e15302 : y = (M.op y y) := by grind
      clear b1e15301
      have b1e15422 : y = (σ y) := by
        first
        | (have i₁ := b1e7007
           have i₂ := b1e15302
           grind)
        | exact superpose b1e15302 b1e7007
        | exact resolve b1e7007 b1e15302
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e7007
      have b1e15595 : y ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e15422
           grind)
        | exact superpose b1e15422 b1e18
        | exact resolve b1e18 b1e15422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e15422
      have b1e15637 : y ≠ (M.op y y) := by
        first
        | (have i₁ := b1e15595
           have i₂ := b1e12410
           grind)
        | exact superpose b1e12410 b1e15595
        | exact resolve b1e15595 b1e12410
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e12410 b1e15595
      have b1e15641 : False := by grind
      exact b1e15641
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
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
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
      have b2e30 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ y)) = (M.op (σ y) (σ y)) := by
        intro X0
        first
        | (have i₁ := b2e10 (σ y) (σ x) X0
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X2 (M.op X2 X0) X3
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
      have b2e34 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ y) X0) := by
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
      have b2e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X3 X2 (M.op X2 X0)
           have i₂ := b2e10 X2 X0 X1
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e38 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X1 X2) ∨ (k X0 (M.op X1 X2)) = X0 := by
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
      have b2e39 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 (M.op X2 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e31 X0 X1 X2 X3
           have i₂ := b2e35 X2 X0 X3 X2
           grind)
        | exact superpose b2e35 b2e31
        | exact resolve b2e31 b2e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e31
      have b2e46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
      have b2e48 : x = (M.op x y) ∨ y = (M.op y x) := by
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
      have b2e49 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
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
      have b2e50 : (σ (M.op x y)) = (σ x) := by
        first
        | (have r₁ := b2e49
           have r₂ := b2e17
           grind)
        | exact resolve b2e49 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e49
      have b2e51 : x = (M.op x y) := by
        first
        | (have r₁ := b2e48
           have r₂ := b2e17
           grind)
        | exact resolve b2e48 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e48
      have b2e53 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b2e10 X0 x y
           have i₂ := b2e51
           grind)
        | exact superpose b2e51 b2e10
        | exact resolve b2e10 b2e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e62 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      clear b2e23
      have b2e81 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (σ y) X0) X1) := by
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
      have b2e82 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op x X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e33 x X0 X1 y
           have i₂ := b2e51
           grind)
        | exact superpose b2e51 b2e33
        | exact resolve b2e33 b2e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e111 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op (M.op X0 X2) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e33 X0 (M.op X0 (σ y)) X1 X2
           have i₂ := b2e34 X0
           grind)
        | exact superpose b2e34 b2e33
        | exact resolve b2e33 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e112 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op X1 (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X1 X0 (M.op X0 (σ y))
           have i₂ := b2e34 X0
           grind)
        | exact superpose b2e34 b2e10
        | exact resolve b2e10 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e113 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ y)) X1) X0) = (M.op X0 (M.op (σ y) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 (M.op X0 (σ y)) X1
           have i₂ := b2e34 X0
           grind)
        | exact superpose b2e34 b2e10
        | exact resolve b2e10 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e117 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (σ y) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e113 X0 X1
           have i₂ := b2e35 X0 (σ y) X1 X0
           grind)
        | exact superpose b2e35 b2e113
        | exact resolve b2e113 b2e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e35 b2e113
      have b2e118 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op X1 (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e112 X0 X1
           have i₂ := b2e81 X0 X1
           grind)
        | exact superpose b2e81 b2e112
        | exact resolve b2e112 b2e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e112
      have b2e119 : ∀ X0 X1 X2 : G, (M.op (σ y) X1) = (M.op (M.op X0 X2) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e111 X0 X1 X2
           have i₂ := b2e81 X0 X1
           grind)
        | exact superpose b2e81 b2e111
        | exact resolve b2e111 b2e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e81 b2e111
      have b2e123 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op x (M.op x X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e53 (M.op X0 X1)
           have i₂ := b2e10 x X0 X1
           grind)
        | exact superpose b2e10 b2e53
        | exact resolve b2e53 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e143 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (σ y) (M.op x (M.op x X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e123 X0 X1
           have i₂ := b2e119 X0 (M.op x (M.op x X0)) X1
           grind)
        | exact superpose b2e119 b2e123
        | exact resolve b2e123 b2e119
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e123
      have b2e150 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (σ y) (M.op (σ y) x)) := by
        intro X0 X1
        first
        | (have i₁ := b2e143 X0 X1
           have i₂ := b2e118 X0 x
           grind)
        | exact superpose b2e118 b2e143
        | exact resolve b2e143 b2e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e143
      have b2e157 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op x (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b2e150 X0 X1
           have i₂ := b2e53 (σ y)
           grind)
        | exact superpose b2e53 b2e150
        | exact resolve b2e150 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e150
      have b2e189 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (σ y) x) X0) := by
        intro X0
        first
        | (have i₁ := b2e82 (M.op x (σ y)) X0
           have i₂ := b2e34 x
           grind)
        | exact superpose b2e34 b2e82
        | exact resolve b2e82 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e202 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X1) = (M.op X1 (M.op X1 (M.op x X2))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 X1 (M.op x X2) X0
           have i₂ := b2e82 X2 X0
           grind)
        | exact superpose b2e82 b2e10
        | exact resolve b2e10 b2e82
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e206 : ∀ X0 : G, (M.op (σ y) (M.op x X0)) = (M.op x (M.op (M.op x X0) (σ y))) := by
        intro X0
        first
        | (have i₁ := b2e34 (M.op x X0)
           have i₂ := b2e82 X0 (M.op (M.op x X0) (σ y))
           grind)
        | exact superpose b2e82 b2e34
        | exact resolve b2e34 b2e82
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34
      have b2e209 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op (M.op x X0) (M.op x x)) := by
        intro X0
        first
        | (have i₁ := b2e53 (M.op x X0)
           have i₂ := b2e82 X0 x
           grind)
        | exact superpose b2e82 b2e53
        | exact resolve b2e53 b2e82
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e82
      have b2e210 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op (σ y) (M.op x x)) := by
        intro X0
        first
        | (have i₁ := b2e209 X0
           have i₂ := b2e119 x (M.op x x) X0
           grind)
        | exact superpose b2e119 b2e209
        | exact resolve b2e209 b2e119
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e209
      have b2e212 : ∀ X0 : G, (M.op x (σ y)) = (M.op (σ y) (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b2e206 X0
           have i₂ := b2e157 (M.op x X0) (σ y)
           grind)
        | exact superpose b2e157 b2e206
        | exact resolve b2e206 b2e157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e206
      have b2e215 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op X1 (M.op (σ y) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e202 X0 X1 x
           have i₂ := b2e117 X1 (M.op x x)
           grind)
        | exact superpose b2e117 b2e202
        | exact resolve b2e202 b2e117
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e202
      have b2e220 : ∀ X0 : G, (M.op (σ y) X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b2e189 X0
           have i₂ := b2e119 (σ y) X0 x
           grind)
        | exact superpose b2e119 b2e189
        | exact resolve b2e189 b2e119
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e189
      have b2e221 : (M.op (σ y) x) = (M.op (σ y) (M.op x x)) := by
        first
        | (have i₁ := b2e210 x
           have i₂ := b2e118 x x
           grind)
        | exact superpose b2e118 b2e210
        | exact resolve b2e210 b2e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e210
      have b2e225 : ∀ X1 : G, (M.op (σ y) X1) = (M.op X1 (M.op (σ y) X1)) := by
        intro X1
        first
        | (have i₁ := b2e215 x X1
           have i₂ := b2e119 x X1 x
           grind)
        | exact superpose b2e119 b2e215
        | exact resolve b2e215 b2e119
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e215
      have b2e227 : (M.op (σ y) x) = (M.op x (σ y)) := by
        first
        | (have i₁ := b2e221
           have i₂ := b2e212 x
           grind)
        | exact superpose b2e212 b2e221
        | exact resolve b2e221 b2e212
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e212 b2e221
      have b2e230 : ∀ X1 : G, (M.op x X1) = (M.op X1 (M.op x X1)) := by
        intro X1
        first
        | (have i₁ := b2e225 x
           have i₂ := b2e220 x
           grind)
        | exact superpose b2e220 b2e225
        | exact resolve b2e225 b2e220
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e225
      have b2e231 : (M.op x (σ y)) = (M.op x x) := by
        first
        | (have i₁ := b2e227
           have i₂ := b2e220 x
           grind)
        | exact superpose b2e220 b2e227
        | exact resolve b2e227 b2e220
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e227
      have b2e413 : (σ y) = (M.op x (σ x)) := by
        first
        | (have i₁ := b2e18
           have i₂ := b2e220 (σ x)
           grind)
        | exact superpose b2e220 b2e18
        | exact resolve b2e18 b2e220
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e472 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e39 X0 X1 (M.op X0 X1) X3
           have i₂ := b2e10 (M.op X0 X1) (M.op X0 X1) X2
           grind)
        | exact superpose b2e10 b2e39
        | exact resolve b2e39 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e39
      have b2e569 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) = (M.op (σ y) (M.op (M.op X0 X1) X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e472 X0 X1 X2 X3
           have i₂ := b2e119 X0 (M.op (M.op X0 X1) X3) X1
           grind)
        | exact superpose b2e119 b2e472
        | exact resolve b2e472 b2e119
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e472
      have b2e616 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) = (M.op x (M.op (M.op X0 X1) X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e569 X0 X1 X2 X3
           have i₂ := b2e220 (M.op (M.op X0 X1) X3)
           grind)
        | exact superpose b2e220 b2e569
        | exact resolve b2e569 b2e220
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e569
      have b2e652 : ∀ X0 X1 X2 : G, (M.op x (σ y)) = (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e616 X0 X1 X2 x
           have i₂ := b2e157 (M.op X0 X1) x
           grind)
        | exact superpose b2e157 b2e616
        | exact resolve b2e616 b2e157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e616
      have b2e679 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op x (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b2e652 X0 X1 x
           have i₂ := b2e119 (M.op X0 X1) (M.op X0 X1) x
           grind)
        | exact superpose b2e119 b2e652
        | exact resolve b2e652 b2e119
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e652
      have b2e702 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op x x) := by
        intro X0 X1
        first
        | (have i₁ := b2e679 X0 X1
           have i₂ := b2e231
           grind)
        | exact superpose b2e231 b2e679
        | exact resolve b2e679 b2e231
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e679
      have b2e718 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op x x) := by
        intro X0 X1
        first
        | (have i₁ := b2e702 X0 X1
           have i₂ := b2e220 (M.op X0 X1)
           grind)
        | exact superpose b2e220 b2e702
        | exact resolve b2e702 b2e220
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e702
      have b2e1305 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X2) X3)) ≠ (M.op X3 X4) ∨ (M.op X0 X2) = (k (M.op X0 X2) (M.op X3 X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e38 (M.op X0 X2) X3 X4
           have i₂ := b2e33 X0 X2 (M.op (M.op X0 X2) X3) X1
           grind)
        | (have i₁ := b2e38 (M.op X0 X2) X3 X4
           have i₂ := b2e33 X0 X1 (M.op (M.op X0 X2) X3) X2
           grind)
        | exact superpose b2e33 b2e38
        | (have j0 := b2e38 (M.op X0 X2) X3 X4
           grind)
        | (have r₁ := b2e38 (M.op X0 X1) (M.op X0 X3) (M.op (M.op X0 X1) (M.op X0 X3))
           have r₂ := b2e33 X0 X1 (M.op (M.op X0 X1) (M.op X0 X3)) X3
           grind)
        | (have r₁ := b2e38 (M.op X0 X3) (M.op X0 X1) (M.op (M.op X0 X3) (M.op X0 X1))
           have r₂ := b2e33 X0 X1 (M.op (M.op X0 X3) (M.op X0 X1)) X3
           grind)
        | exact resolve b2e38 b2e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e33
      have b2e1323 : ∀ X0 : G, (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have j0 := b2e38 X0 X0 (M.op X0 X0)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e38
      have b2e1324 : ∀ X0 : G, (k X0 (M.op (σ y) X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b2e1323 X0
           have i₂ := b2e118 X0 X0
           grind)
        | exact superpose b2e118 b2e1323
        | exact resolve b2e1323 b2e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e118 b2e1323
      have b2e1338 : ∀ X0 X2 X3 X4 : G, (M.op X3 X4) ≠ (M.op (σ y) (M.op (M.op X0 X2) X3)) ∨ (M.op X0 X2) = (k (M.op X0 X2) (M.op X3 X4)) := by
        intro X0 X2 X3 X4
        first
        | (have i₁ := b2e1305 X0 x X2 X3 X4
           have i₂ := b2e119 X0 (M.op (M.op X0 X2) X3) x
           grind)
        | exact superpose b2e119 b2e1305
        | (have j0 := b2e1305 X0 x X2 X3 X4
           grind)
        | (have r₁ := b2e1305 X0 X2 X2 (σ y) (M.op (M.op X0 X2) (σ y))
           have r₂ := b2e119 X0 (M.op (M.op X0 X2) (σ y)) X2
           grind)
        | exact resolve b2e1305 b2e119
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1305
      have b2e1364 : ∀ X0 : G, (k X0 (M.op x X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b2e1324 X0
           have i₂ := b2e220 X0
           grind)
        | exact superpose b2e220 b2e1324
        | exact resolve b2e1324 b2e220
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1324
      have b2e1378 : ∀ X0 X2 X3 X4 : G, (M.op X3 X4) ≠ (M.op x (M.op (M.op X0 X2) X3)) ∨ (M.op X0 X2) = (k (M.op X0 X2) (M.op X3 X4)) := by
        intro X0 X2 X3 X4
        first
        | (have i₁ := b2e1338 X0 X2 X3 X4
           have i₂ := b2e220 (M.op (M.op X0 X2) X3)
           grind)
        | exact superpose b2e220 b2e1338
        | (have j0 := b2e1338 X0 X2 X3 X4
           grind)
        | (have r₁ := b2e1338 X0 X2 x (M.op (M.op X0 X2) x)
           have r₂ := b2e220 (M.op (M.op X0 X2) x)
           grind)
        | exact resolve b2e1338 b2e220
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1338
      have b2e1411 : ∀ X0 X2 X3 X4 : G, (M.op X3 X4) ≠ (M.op x (σ y)) ∨ (M.op X0 X2) = (k (M.op X0 X2) (M.op X3 X4)) := by
        intro X0 X2 X3 X4
        first
        | (have i₁ := b2e1378 X0 X2 X3 X4
           have i₂ := b2e157 (M.op X0 X2) X3
           grind)
        | exact superpose b2e157 b2e1378
        | (have j0 := b2e1378 X0 X2 X3 X4
           grind)
        | (have r₁ := b2e1378 X0 X2 x (σ y)
           have r₂ := b2e157 (M.op X0 X2) x
           grind)
        | exact resolve b2e1378 b2e157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1378
      have b2e1441 : ∀ X0 X2 X3 X4 : G, (M.op X3 X4) ≠ (M.op x x) ∨ (M.op X0 X2) = (k (M.op X0 X2) (M.op X3 X4)) := by
        intro X0 X2 X3 X4
        first
        | (have i₁ := b2e1411 X0 X2 X3 X4
           have i₂ := b2e231
           grind)
        | exact superpose b2e231 b2e1411
        | (have j0 := b2e1411 X0 X2 X3 X4
           grind)
        | (have r₁ := b2e1411 X0 X2 x x
           have r₂ := b2e231
           grind)
        | exact resolve b2e1411 b2e231
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1411
      have b2e1503 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op x x)) := by
        intro X0 X1
        first
        | (have i₁ := b2e1364 (M.op X0 X1)
           have i₂ := b2e718 X0 X1
           grind)
        | exact superpose b2e718 b2e1364
        | exact resolve b2e1364 b2e718
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e2317 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e30 (σ X0)
           have i₂ := b2e46 X0 x
           grind)
        | exact superpose b2e46 b2e30
        | (have j1 := b2e46 X0 x
           grind)
        | exact resolve b2e30 b2e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e30
      have b2e2338 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b2e46 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46
      have b2e2356 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e2317 X0
           have i₂ := b2e220 (σ y)
           grind)
        | exact superpose b2e220 b2e2317
        | (have j0 := b2e2317 X0
           grind)
        | exact resolve b2e2317 b2e220
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2317
      have b2e2399 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op x x) ∨ (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e2356 X0
           have i₂ := b2e231
           grind)
        | exact superpose b2e231 b2e2356
        | (have j0 := b2e2356 X0
           grind)
        | exact resolve b2e2356 b2e231
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2356
      have b2e2435 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b2e230 (σ x)
           have i₂ := b2e413
           grind)
        | exact superpose b2e413 b2e230
        | exact resolve b2e230 b2e413
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e230
      have b2e2629 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op x (σ X0)))) := by
        intro X0
        first
        | (have i₁ := b2e62 X0 (M.op x (σ X0))
           have i₂ := b2e1364 (σ X0)
           grind)
        | exact superpose b2e1364 b2e62
        | exact resolve b2e62 b2e1364
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e62 b2e1364
      have b2e2641 : ∀ X0 : G, (k X0 (τ (M.op x (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b2e2629 X0
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e2629
        | exact resolve b2e2629 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2629
      have b2e3391 : y = (k y (τ (M.op x x))) := by
        first
        | (have i₁ := b2e2641 y
           have i₂ := b2e231
           grind)
        | exact superpose b2e231 b2e2641
        | exact resolve b2e2641 b2e231
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2641
      have b2e8544 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
        first
        | (have i₁ := b2e2338 (M.op x x)
           have i₂ := b2e1503 x x
           grind)
        | exact superpose b2e1503 b2e2338
        | (have j0 := b2e2338 (M.op x x)
           grind)
        | exact resolve b2e2338 b2e1503
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1503 b2e2338
      have b2e8549 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by grind
      clear b2e8544
      have b2e14695 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (M.op (σ y) (σ (M.op x x)))) := by
        first
        | (have i₁ := b2e117 (σ (M.op x x)) (σ (M.op x x))
           have i₂ := b2e8549
           grind)
        | exact superpose b2e8549 b2e117
        | exact resolve b2e117 b2e8549
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e14697 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x x)) X0) := by
        intro X0
        first
        | (have i₁ := b2e119 (σ (M.op x x)) X0 (σ (M.op x x))
           have i₂ := b2e8549
           grind)
        | exact superpose b2e8549 b2e119
        | exact resolve b2e119 b2e8549
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e119
      have b2e14706 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x x)) X0) := by
        intro X0
        first
        | (have i₁ := b2e14697 X0
           have i₂ := b2e220 X0
           grind)
        | exact superpose b2e220 b2e14697
        | exact resolve b2e14697 b2e220
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e14697
      have b2e14708 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (M.op x (σ (M.op x x)))) := by
        first
        | (have i₁ := b2e14695
           have i₂ := b2e220 (σ (M.op x x))
           grind)
        | exact superpose b2e220 b2e14695
        | exact resolve b2e14695 b2e220
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e220 b2e14695
      have b2e14742 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op x (M.op x (σ (M.op x x)))) := by
        first
        | (have i₁ := b2e14708
           have i₂ := b2e14706 (M.op x (σ (M.op x x)))
           grind)
        | exact superpose b2e14706 b2e14708
        | exact resolve b2e14708 b2e14706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e14708
      have b2e14768 : (M.op x (M.op (σ y) x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
        first
        | (have i₁ := b2e14742
           have i₂ := b2e117 x (σ (M.op x x))
           grind)
        | exact superpose b2e117 b2e14742
        | exact resolve b2e14742 b2e117
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e117 b2e14742
      have b2e14788 : (M.op x (M.op (σ y) x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b2e14768
           have i₂ := b2e8549
           grind)
        | exact superpose b2e8549 b2e14768
        | exact resolve b2e14768 b2e8549
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e8549 b2e14768
      have b2e14804 : (M.op x (σ y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b2e14788
           have i₂ := b2e157 (σ y) x
           grind)
        | exact superpose b2e157 b2e14788
        | exact resolve b2e14788 b2e157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e157 b2e14788
      have b2e14813 : (M.op x x) = (σ (M.op x x)) := by
        first
        | (have i₁ := b2e14804
           have i₂ := b2e231
           grind)
        | exact superpose b2e231 b2e14804
        | exact resolve b2e14804 b2e231
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e231 b2e14804
      have b2e15025 : (M.op x x) = (τ (M.op x x)) := by
        first
        | (have i₁ := b2e11 (M.op x x)
           have i₂ := b2e14813
           grind)
        | exact superpose b2e14813 b2e11
        | exact resolve b2e11 b2e14813
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e15829 : y = (k y (M.op x x)) := by
        first
        | (have i₁ := b2e3391
           have i₂ := b2e15025
           grind)
        | exact superpose b2e15025 b2e3391
        | exact resolve b2e3391 b2e15025
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3391 b2e15025
      have b2e15881 : y = (M.op y (M.op x x)) ∨ (M.op x x) = (M.op (M.op x x) y) := by
        first
        | (have i₁ := b2e14 y (M.op x x)
           have i₂ := b2e15829
           grind)
        | exact superpose b2e15829 b2e14
        | (have j0 := b2e14 (M.op x x) y
           grind)
        | exact resolve b2e14 b2e15829
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e15829
      have b2e15882 : (M.op x x) = (M.op y (M.op y x)) ∨ y = (M.op y (M.op x x)) := by
        first
        | (have i₁ := b2e15881
           have i₂ := b2e10 y x x
           grind)
        | exact superpose b2e10 b2e15881
        | exact resolve b2e15881 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e15881
      have b2e15885 : (M.op x y) = (M.op x x) ∨ y = (M.op y (M.op x x)) := by
        first
        | (have i₁ := b2e15882
           have i₂ := b2e53 y
           grind)
        | exact superpose b2e53 b2e15882
        | exact resolve b2e15882 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e53 b2e15882
      have b2e15888 : y = (M.op y (M.op x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b2e15885
           have i₂ := b2e51
           grind)
        | exact superpose b2e51 b2e15885
        | exact resolve b2e15885 b2e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e15885
      have b2e17290 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b2e718 y (M.op x x)
           have i₂ := b2e15888
           grind)
        | exact superpose b2e15888 b2e718
        | exact resolve b2e718 b2e15888
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e718 b2e15888
      have b2e17298 : x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b2e17290
           have i₂ := b2e51
           grind)
        | exact superpose b2e51 b2e17290
        | exact resolve b2e17290 b2e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e51 b2e17290
      have b2e17299 : x = (M.op x x) := by grind
      clear b2e17298
      have b2e17534 : x = (σ x) := by
        first
        | (have i₁ := b2e14813
           have i₂ := b2e17299
           grind)
        | exact superpose b2e17299 b2e14813
        | exact resolve b2e14813 b2e17299
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e17583 : ∀ X0 X1 : G, x ≠ x ∨ (M.op X0 X1) = (k (M.op X0 X1) x) := by
        intro X0 X1
        first
        | (have i₁ := b2e1441 X0 x x x
           have i₂ := b2e17299
           grind)
        | exact superpose b2e17299 b2e1441
        | exact resolve b2e1441 b2e17299
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1441
      have b2e17587 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) x) := by
        intro X0 X1
        first
        | (have j0 := b2e17583 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e17583
      have b2e17720 : (M.op x (σ x)) = (σ (k (M.op x x) x)) ∨ (M.op (σ x) (σ y)) = (M.op x x) := by
        first
        | (have i₁ := b2e14706 (σ x)
           have i₂ := b2e2399 (M.op x x)
           grind)
        | exact superpose b2e2399 b2e14706
        | exact resolve b2e14706 b2e2399
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2399 b2e14706
      have b2e17809 : (M.op x (σ x)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op x x) := by
        first
        | (have i₁ := b2e17720
           have i₂ := b2e17587 x x
           grind)
        | exact superpose b2e17587 b2e17720
        | exact resolve b2e17720 b2e17587
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e17587 b2e17720
      have b2e17894 : (M.op x (σ x)) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op x x) := by
        first
        | (have i₁ := b2e17809
           have i₂ := b2e14813
           grind)
        | exact superpose b2e14813 b2e17809
        | exact resolve b2e17809 b2e14813
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e14813 b2e17809
      have b2e17964 : x = (M.op x (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op x x) := by
        first
        | (have i₁ := b2e17894
           have i₂ := b2e17299
           grind)
        | exact superpose b2e17299 b2e17894
        | exact resolve b2e17894 b2e17299
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e17894
      have b2e18021 : x = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op x x) := by
        first
        | (have i₁ := b2e17964
           have i₂ := b2e413
           grind)
        | exact superpose b2e413 b2e17964
        | exact resolve b2e17964 b2e413
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e413 b2e17964
      have b2e18052 : x = (M.op (σ x) (σ y)) ∨ x = (σ y) := by
        first
        | (have i₁ := b2e18021
           have i₂ := b2e17299
           grind)
        | exact superpose b2e17299 b2e18021
        | exact resolve b2e18021 b2e17299
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e18021
      have b2e18068 : x = (σ y) ∨ x = (σ y) := by
        first
        | (have i₁ := b2e18052
           have i₂ := b2e2435
           grind)
        | exact superpose b2e2435 b2e18052
        | exact resolve b2e18052 b2e2435
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2435 b2e18052
      have b2e18069 : x = (σ y) := by grind
      clear b2e18068
      have b2e18090 : (σ (M.op x y)) ≠ (M.op (σ x) x) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e18069
           grind)
        | exact superpose b2e18069 b2e16
        | exact resolve b2e16 b2e18069
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e18069
      have b2e18143 : (σ (M.op x y)) ≠ (M.op x x) := by
        first
        | (have i₁ := b2e18090
           have i₂ := b2e17534
           grind)
        | exact superpose b2e17534 b2e18090
        | exact resolve b2e18090 b2e17534
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e18090
      have b2e18149 : x ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b2e18143
           have i₂ := b2e17299
           grind)
        | exact superpose b2e17299 b2e18143
        | exact resolve b2e18143 b2e17299
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e17299 b2e18143
      have b2e18153 : x ≠ (σ x) := by
        first
        | (have i₁ := b2e18149
           have i₂ := b2e50
           grind)
        | exact superpose b2e50 b2e18149
        | exact resolve b2e18149 b2e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50 b2e18149
      have b2e18154 : False := by grind
      exact b2e18154
    · have b3e14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op y x) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
      have b3e761 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
      clear b3e34
      have b3e812 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have r₁ := b3e761
           have r₂ := b3e18
           grind)
        | exact resolve b3e761 b3e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e761
      have b3e817 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b3e812
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e812
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e812 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e812
      have b3e818 : y = (M.op y x) := by grind
      clear b3e817
      have b3e819 : False := by grind
      exact b3e819

/-- `Equation4412`: `x ◇ (x ◇ y) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4412 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4412 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4412.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          grind
        have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
        have b0e37 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
          intro X0 X1 X3
          first
          | (have i₁ := b0e11 x X0 X3
             have i₂ := b0e11 x X0 X1
             grind)
          | exact superpose b0e11 b0e11
          | exact resolve b0e11 b0e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e38 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b0e11 X2 X3 (M.op X3 X0)
             have i₂ := b0e11 X3 X0 X1
             grind)
          | exact superpose b0e11 b0e11
          | exact resolve b0e11 b0e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e41 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op y x) := by
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
        have b0e42 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b0e11 X0 y y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e11
          | exact resolve b0e11 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e44 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b0e42 X0
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e42
          | exact resolve b0e42 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e42
        have b0e49 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e11 X0 X1 (M.op X1 y)
             have i₂ := b0e44 X1
             grind)
          | exact superpose b0e44 b0e11
          | exact resolve b0e11 b0e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b0e16 X0 X1
             have i₂ := b0e15 (σ X0) (σ X1)
             grind)
          | exact superpose b0e15 b0e16
          | (have j1 := b0e15 (σ X0) (σ X1)
             grind)
          | exact resolve b0e16 b0e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e76 : (M.op x y) = (M.op y x) := by
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
        have b0e115 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y X0) := by
          intro X0 X1
          first
          | (have i₁ := b0e37 X0 X1 (M.op X0 y)
             have i₂ := b0e44 X0
             grind)
          | exact superpose b0e44 b0e37
          | exact resolve b0e37 b0e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e120 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X3) (M.op X1 X2)) = (M.op (M.op X0 (M.op X0 X1)) (M.op X1 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b0e37 (M.op X1 X2) X3 X1
             have i₂ := b0e11 X0 X1 X2
             grind)
          | exact superpose b0e11 b0e37
          | exact resolve b0e37 b0e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e37
        have b0e150 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X3) (M.op X1 X2)) = (M.op (M.op y X1) (M.op X1 X2)) := by
          intro X1 X2 X3
          first
          | (have i₁ := b0e120 x X1 X2 X3
             have i₂ := b0e49 x X1
             grind)
          | exact superpose b0e49 b0e120
          | exact resolve b0e120 b0e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e120
        have b0e158 : ∀ X1 X2 : G, (M.op (M.op y X1) (M.op X1 X2)) = (M.op y (M.op X1 X2)) := by
          intro X1 X2
          first
          | (have i₁ := b0e150 X1 X2 x
             have i₂ := b0e115 (M.op X1 X2) x
             grind)
          | exact superpose b0e115 b0e150
          | exact resolve b0e150 b0e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e150
        have b0e164 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b0e49 X0 (M.op X0 y)
             have i₂ := b0e44 X0
             grind)
          | exact superpose b0e44 b0e49
          | exact resolve b0e49 b0e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e44
        have b0e171 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
          first
          | (have i₁ := b0e49 (σ x) (σ x)
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e49
          | exact resolve b0e49 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e3917 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 X1
             have i₂ := b0e61 X0 X1
             grind)
          | exact superpose b0e61 b0e12
          | (have j1 := b0e61 X0 X1
             grind)
          | exact resolve b0e12 b0e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e3950 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b0e61 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e61
        have b0e4114 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e171
             grind)
          | exact superpose b0e171 b0e17
          | exact resolve b0e17 b0e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e171
        have b0e4147 : (M.op y (σ x)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b0e4114
             have i₂ := b0e76
             grind)
          | exact superpose b0e76 b0e4114
          | exact resolve b0e4114 b0e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e76 b0e4114
        have b0e4899 : ∀ X0 : G, (M.op y (M.op y y)) = X0 ∨ (M.op (M.op y y) X0) = (k (M.op y y) X0) := by
          intro X0
          first
          | (have i₁ := b0e15 (M.op y y) X0
             have i₂ := b0e158 y y
             grind)
          | exact superpose b0e158 b0e15
          | (have j0 := b0e15 (M.op y y) X0
             grind)
          | exact resolve b0e15 b0e158
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e158
        have b0e4940 : ∀ X0 : G, (M.op y y) = X0 ∨ (M.op (M.op y y) X0) = (k (M.op y y) X0) := by
          intro X0
          first
          | (have i₁ := b0e4899 X0
             have i₂ := b0e164 y
             grind)
          | exact superpose b0e164 b0e4899
          | (have j0 := b0e4899 X0
             grind)
          | exact resolve b0e4899 b0e164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e164 b0e4899
        have b0e4967 : ∀ X0 : G, y = X0 ∨ (M.op (M.op y y) X0) = (k (M.op y y) X0) := by
          intro X0
          first
          | (have i₁ := b0e4940 X0
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e4940
          | (have j0 := b0e4940 X0
             grind)
          | exact resolve b0e4940 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e4940
        have b0e4984 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b0e4967 X0
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e4967
          | (have j0 := b0e4967 X0
             grind)
          | exact resolve b0e4967 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e4967
        have b0e8954 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e3950 y
             have i₂ := b0e23
             grind)
          | exact superpose b0e23 b0e3950
          | (have j0 := b0e3950 y
             grind)
          | exact resolve b0e3950 b0e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e23 b0e3950
        have b0e8959 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b0e8954
        have b0e8987 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ y) (σ y)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e38 (σ y) (σ y) X0 X1
             have i₂ := b0e8959
             grind)
          | exact superpose b0e8959 b0e38
          | exact resolve b0e38 b0e8959
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e38
        have b0e8994 : (M.op y (σ y)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e115 (σ y) (σ y)
             have i₂ := b0e8959
             grind)
          | exact superpose b0e8959 b0e115
          | exact resolve b0e115 b0e8959
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e115
        have b0e9007 : (σ y) = (M.op y (σ y)) := by
          first
          | (have i₁ := b0e8994
             have i₂ := b0e8959
             grind)
          | exact superpose b0e8959 b0e8994
          | exact resolve b0e8994 b0e8959
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e8994
        have b0e9014 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e8987 X0 X1
             have i₂ := b0e8959
             grind)
          | exact superpose b0e8959 b0e8987
          | exact resolve b0e8987 b0e8959
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e8987
        have b0e9030 : ∀ X1 : G, (M.op y X1) = (M.op (σ y) X1) := by
          intro X1
          first
          | (have i₁ := b0e9014 x X1
             have i₂ := b0e49 x X1
             grind)
          | exact superpose b0e49 b0e9014
          | exact resolve b0e9014 b0e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e49 b0e9014
        have b0e16093 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (τ (M.op (σ y) (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b0e9030 (σ X0)
             have i₂ := b0e3917 y X0
             grind)
          | exact superpose b0e3917 b0e9030
          | (have j1 := b0e3917 y X0
             grind)
          | exact resolve b0e9030 b0e3917
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e3917 b0e9030
        have b0e16152 : ∀ X0 : G, (τ (σ y)) = X0 ∨ (M.op y (σ X0)) = (σ (k y X0)) := by
          intro X0
          first
          | (have i₁ := b0e16093 X0
             have i₂ := b0e8959
             grind)
          | exact superpose b0e8959 b0e16093
          | (have j0 := b0e16093 X0
             grind)
          | exact resolve b0e16093 b0e8959
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e8959 b0e16093
        have b0e16180 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b0e16152 X0
             have i₂ := b0e12 y
             grind)
          | exact superpose b0e12 b0e16152
          | (have j0 := b0e16152 X0
             grind)
          | exact resolve b0e16152 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e16152
        have b0e20449 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ y = X0 ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b0e16180 X0
             have i₂ := b0e4984 X0
             grind)
          | exact superpose b0e4984 b0e16180
          | (have j0 := b0e16180 X0
             have j1 := b0e4984 X0
             grind)
          | exact resolve b0e16180 b0e4984
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e4984 b0e16180
        have b0e20500 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b0e20449 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e20449
        have b0e23220 : (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ x = y := by
          first
          | (have i₁ := b0e4147
             have i₂ := b0e20500 x
             grind)
          | exact superpose b0e20500 b0e4147
          | (have j1 := b0e20500 x
             grind)
          | (have r₁ := b0e4147
             have r₂ := b0e20500 x
             grind)
          | exact resolve b0e4147 b0e20500
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e20500
        have b0e23257 : x = y := by grind
        clear b0e23220
        have b0e24861 : (M.op y (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b0e4147
             have i₂ := b0e23257
             grind)
          | exact superpose b0e23257 b0e4147
          | exact resolve b0e4147 b0e23257
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e4147 b0e23257
        have b0e24868 : (σ y) ≠ (M.op y (σ y)) := by
          first
          | (have i₁ := b0e24861
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e24861
          | exact resolve b0e24861 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e24861
        have b0e24877 : False := by grind
        exact b0e24877
      · have b1e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          grind
        have b1e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
        have b1e29 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e11 (σ x) (σ x) X0
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e11
          | exact resolve b1e11 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e11 x X0 X3
             have i₂ := b1e11 x X0 X1
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11 X2 X3 (M.op X3 X0)
             have i₂ := b1e11 X3 X0 X1
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (M.op (σ y) (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e11 X0 (σ x) (σ x)
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e11
          | exact resolve b1e11 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op y x) := by
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
        have b1e35 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e11 X0 X1 x
             have i₂ := b1e11 X2 X1 x
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b1e34 x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e34
          | exact resolve b1e34 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : ∀ X1 : G, (M.op y x) = (M.op (M.op x X1) x) := by
          intro X1
          first
          | (have i₁ := b1e11 x x X1
             have i₂ := b1e34 x
             grind)
          | exact superpose b1e34 b1e11
          | exact resolve b1e11 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op y x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 X0 X1 (M.op X1 x)
             have i₂ := b1e34 X1
             grind)
          | exact superpose b1e34 b1e11
          | exact resolve b1e11 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e47 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b1e62 : (M.op y x) = (M.op (M.op y x) x) := by
          first
          | (have i₁ := b1e39 (M.op x x)
             have i₂ := b1e34 x
             grind)
          | exact superpose b1e34 b1e39
          | exact resolve b1e39 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e98 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op y x) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e30 X0 X1 (M.op X0 x)
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e30
          | exact resolve b1e30 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e156 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 x))) = (M.op X1 (M.op y x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e35 X0 (M.op X1 x) X1
             have i₂ := b1e34 X1
             grind)
          | exact superpose b1e34 b1e35
          | exact resolve b1e35 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e163 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b1e35 X0 (σ x) (σ x)
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e35
          | exact resolve b1e35 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e187 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e163 x
             have i₂ := b1e33 x
             grind)
          | exact superpose b1e33 b1e163
          | exact resolve b1e163 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e163
        have b1e264 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e47 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e276 : (M.op y x) ≠ (M.op y x) ∨ (M.op y x) = (k (M.op y x) x) := by
          first
          | (have i₁ := b1e264 (M.op y x) x
             have i₂ := b1e62
             grind)
          | exact superpose b1e62 b1e264
          | (have j0 := b1e264 (M.op y x) x
             grind)
          | (have r₁ := b1e264 (M.op y x) x
             have r₂ := b1e62
             grind)
          | exact resolve b1e264 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62 b1e264
        have b1e280 : (M.op y x) = (k (M.op y x) x) := by grind
        clear b1e276
        have b1e286 : (M.op (σ x) (σ y)) = (M.op (M.op y x) (σ x)) := by
          first
          | (have i₁ := b1e29 (M.op (σ x) x)
             have i₂ := b1e34 (σ x)
             grind)
          | exact superpose b1e34 b1e29
          | exact resolve b1e29 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e315 : (M.op (σ y) (σ x)) = (M.op (M.op y x) (σ x)) := by
          first
          | (have i₁ := b1e286
             have i₂ := b1e187
             grind)
          | exact superpose b1e187 b1e286
          | exact resolve b1e286 b1e187
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e286
        have b1e382 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op (M.op X0 X1) X0) X2)) = (M.op (M.op (M.op X3 X2) X4) (M.op X3 X2)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e11 X3 (M.op X3 X2) X4
             have i₂ := b1e31 X0 X1 X3 X2
             grind)
          | exact superpose b1e31 b1e11
          | exact resolve b1e11 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e415 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op (M.op X0 X1) X0) X2)) = (M.op (M.op y x) (M.op X3 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e382 X0 X1 X2 X3 x
             have i₂ := b1e98 (M.op X3 X2) x
             grind)
          | exact superpose b1e98 b1e382
          | exact resolve b1e382 b1e98
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e98 b1e382
        have b1e893 : ∀ X0 X2 X3 : G, (M.op (M.op y x) X0) = (M.op (M.op (M.op X2 X3) X2) X0) := by
          intro X0 X2 X3
          first
          | (have i₁ := b1e31 X2 X3 x X0
             have i₂ := b1e40 x X0
             grind)
          | exact superpose b1e40 b1e31
          | exact resolve b1e31 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e914 : ∀ X0 X1 X2 X3 : G, (M.op (M.op y x) X0) = (M.op X1 (M.op X1 (M.op (M.op (M.op X2 X3) X2) X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e31 X2 X3 X1 (M.op (M.op (M.op X2 X3) X2) X0)
             have i₂ := b1e40 (M.op (M.op X2 X3) X2) X0
             grind)
          | exact superpose b1e40 b1e31
          | exact resolve b1e31 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e923 : ∀ X0 : G, (M.op y x) = (k (M.op y x) (M.op X0 (M.op X0 (M.op y x)))) := by
          intro X0
          grind
        clear b1e40
        have b1e954 : (M.op y x) = (k (M.op y x) (M.op y (M.op y x))) := by
          first
          | (have i₁ := b1e923 x
             have i₂ := b1e156 x y
             grind)
          | exact superpose b1e156 b1e923
          | exact resolve b1e923 b1e156
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e156 b1e923
        have b1e957 : ∀ X0 X1 : G, (M.op (M.op y x) X0) = (M.op X1 (M.op (M.op y x) (M.op X1 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e914 X0 X1 x x
             have i₂ := b1e415 x x X0 X1
             grind)
          | exact superpose b1e415 b1e914
          | exact resolve b1e914 b1e415
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e415 b1e914
        have b1e974 : (M.op y x) = (k (M.op y x) (M.op y x)) := by
          first
          | (have i₁ := b1e954
             have i₂ := b1e34 y
             grind)
          | exact superpose b1e34 b1e954
          | exact resolve b1e954 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e954
        have b1e2023 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e17
             have i₂ := b1e187
             grind)
          | exact superpose b1e187 b1e17
          | exact resolve b1e17 b1e187
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e187
        have b1e2049 : (M.op (σ y) (σ x)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b1e2023
             have i₂ := b1e37
             grind)
          | exact superpose b1e37 b1e2023
          | exact resolve b1e2023 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37 b1e2023
        have b1e2151 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1
             have i₂ := b1e52 X0 X1
             grind)
          | exact superpose b1e52 b1e12
          | (have j1 := b1e52 X0 X1
             grind)
          | exact resolve b1e12 b1e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2188 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e52 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e51951 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by
          first
          | (have i₁ := b1e2188 (M.op y x)
             have i₂ := b1e974
             grind)
          | exact superpose b1e974 b1e2188
          | (have j0 := b1e2188 (M.op y x)
             grind)
          | exact resolve b1e2188 b1e974
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e974 b1e2188
        have b1e51963 : (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by grind
        clear b1e51951
        have b1e58401 : ∀ X0 : G, (M.op (M.op y x) X0) = (M.op (M.op (σ (M.op y x)) (σ (M.op y x))) X0) := by
          intro X0
          first
          | (have i₁ := b1e893 X0 (σ (M.op y x)) (σ (M.op y x))
             have i₂ := b1e51963
             grind)
          | exact superpose b1e51963 b1e893
          | exact resolve b1e893 b1e51963
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e893
        have b1e58429 : ∀ X0 : G, (M.op (M.op y x) X0) = (M.op (σ (M.op y x)) X0) := by
          intro X0
          first
          | (have i₁ := b1e58401 X0
             have i₂ := b1e51963
             grind)
          | exact superpose b1e51963 b1e58401
          | exact resolve b1e58401 b1e51963
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58401
        have b1e171582 : ∀ X0 : G, (M.op (M.op y x) (σ X0)) = (σ (k (M.op y x) X0)) ∨ (τ (M.op (σ (M.op y x)) (σ (M.op y x)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e58429 (σ X0)
             have i₂ := b1e2151 (M.op y x) X0
             grind)
          | exact superpose b1e2151 b1e58429
          | (have j1 := b1e2151 (M.op y x) X0
             grind)
          | exact resolve b1e58429 b1e2151
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2151 b1e58429
        have b1e171833 : ∀ X0 : G, (τ (σ (M.op y x))) = X0 ∨ (M.op (M.op y x) (σ X0)) = (σ (k (M.op y x) X0)) := by
          intro X0
          first
          | (have i₁ := b1e171582 X0
             have i₂ := b1e51963
             grind)
          | exact superpose b1e51963 b1e171582
          | (have j0 := b1e171582 X0
             grind)
          | exact resolve b1e171582 b1e51963
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51963 b1e171582
        have b1e171920 : ∀ X0 : G, (M.op (M.op y x) (σ X0)) = (σ (k (M.op y x) X0)) ∨ (M.op y x) = X0 := by
          intro X0
          first
          | (have i₁ := b1e171833 X0
             have i₂ := b1e12 (M.op y x)
             grind)
          | exact superpose b1e12 b1e171833
          | (have j0 := b1e171833 X0
             grind)
          | exact resolve b1e171833 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e171833
        have b1e1040680 : (M.op (M.op y x) (σ x)) = (σ (M.op y x)) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b1e171920 x
             have i₂ := b1e280
             grind)
          | exact superpose b1e280 b1e171920
          | (have j0 := b1e171920 x
             grind)
          | exact resolve b1e171920 b1e280
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e280 b1e171920
        have b1e1040683 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b1e1040680
             have i₂ := b1e315
             grind)
          | exact superpose b1e315 b1e1040680
          | exact resolve b1e1040680 b1e315
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e315 b1e1040680
        have b1e1040684 : x = (M.op y x) := by
          first
          | (have r₁ := b1e1040683
             have r₂ := b1e2049
             grind)
          | exact resolve b1e1040683 b1e2049
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2049 b1e1040683
        have b1e1041472 : (M.op x x) = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b1e957 x y
             have i₂ := b1e1040684
             grind)
          | exact superpose b1e1040684 b1e957
          | exact resolve b1e957 b1e1040684
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e957 b1e1040684
        have b1e1042288 : y = (M.op y y) := by
          first
          | (have i₁ := b1e1041472
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e1041472
          | exact resolve b1e1041472 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1041472
        have b1e1042862 : False := by grind
        exact b1e1042862
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b2e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          grind
        have b2e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e18 : y = (M.op x x) := by grind
        have b2e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e20 : y = (M.op y y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b2e22 : x = (k x y) := by grind
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
        have b2e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) (M.op X2 X0)) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e11 X2 (M.op X2 X0) X3
             have i₂ := b2e11 X2 X0 X1
             grind)
          | exact superpose b2e11 b2e11
          | exact resolve b2e11 b2e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e11 x X0 X3
             have i₂ := b2e11 x X0 X1
             grind)
          | exact superpose b2e11 b2e11
          | exact resolve b2e11 b2e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b2e11 X0 y y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e11
          | exact resolve b2e11 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e40 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b2e38 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e38
          | exact resolve b2e38 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38
        have b2e45 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e11 X0 X1 (M.op X1 y)
             have i₂ := b2e40 X1
             grind)
          | exact superpose b2e40 b2e11
          | exact resolve b2e11 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e55 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
        have b2e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b2e88 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e108 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 X1) X0) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e34 X2 X3 (M.op X2 X0)
             have i₂ := b2e11 X2 X0 X1
             grind)
          | exact superpose b2e11 b2e34
          | exact resolve b2e34 b2e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e109 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e34 X0 X1 (M.op X0 y)
             have i₂ := b2e40 X0
             grind)
          | exact superpose b2e40 b2e34
          | exact resolve b2e34 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e40
        have b2e145 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op y X0) X2) := by
          intro X0 X2 X3
          first
          | (have i₁ := b2e108 X0 x X2 X3
             have i₂ := b2e109 X0 x
             grind)
          | exact superpose b2e109 b2e108
          | exact resolve b2e108 b2e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108
        have b2e152 : ∀ X0 X2 : G, (M.op y X2) = (M.op (M.op y X0) X2) := by
          intro X0 X2
          first
          | (have i₁ := b2e145 X0 X2 x
             have i₂ := b2e109 X2 x
             grind)
          | exact superpose b2e109 b2e145
          | exact resolve b2e145 b2e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e145
        have b2e155 : ∀ X0 X1 : G, (M.op y (M.op X1 X0)) = (M.op X1 (M.op y X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e45 X1 (M.op X1 X0)
             have i₂ := b2e45 X1 X0
             grind)
          | exact superpose b2e45 b2e45
          | exact resolve b2e45 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e359 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e52 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e819 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e55 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e820 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e819
             have i₂ := b2e16 x y
             grind)
          | exact superpose b2e16 b2e819
          | exact resolve b2e819 b2e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e819
        have b2e821 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e820
             have i₂ := b2e22
             grind)
          | exact superpose b2e22 b2e820
          | exact resolve b2e820 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22 b2e820
        have b2e830 : (M.op (σ x) (σ x)) = (M.op y (σ y)) := by
          first
          | (have i₁ := b2e45 (σ x) (σ y)
             have i₂ := b2e821
             grind)
          | exact superpose b2e821 b2e45
          | exact resolve b2e45 b2e821
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e831 : (M.op (σ x) (σ x)) = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e109 (σ x) (σ y)
             have i₂ := b2e821
             grind)
          | exact superpose b2e821 b2e109
          | exact resolve b2e109 b2e821
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e821
        have b2e3361 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e56 x x
             grind)
          | exact superpose b2e56 b2e19
          | (have j1 := b2e56 x x
             grind)
          | (have r₁ := b2e19
             have r₂ := b2e56 x y
             grind)
          | exact resolve b2e19 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e3447 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e3361
             have i₂ := b2e831
             grind)
          | exact superpose b2e831 b2e3361
          | exact resolve b2e3361 b2e831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3361
        have b2e3503 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e88
        have b2e3522 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e3503 X0
             have i₂ := b2e12 X0
             grind)
          | exact superpose b2e12 b2e3503
          | exact resolve b2e3503 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3503
        have b2e3556 : x ≠ y ∨ x = (k x x) := by
          first
          | (have i₁ := b2e359 x x
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e359
          | (have j0 := b2e359 x x
             grind)
          | exact resolve b2e359 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e359
        have b2e3723 : (σ y) ≠ (M.op y (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e830
             grind)
          | exact superpose b2e830 b2e19
          | exact resolve b2e19 b2e830
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3730 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ x) X1) (σ x))) = (M.op (M.op (M.op y (σ y)) X0) (M.op y (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b2e32 (σ x) X1 (σ x) x
             have i₂ := b2e830
             grind)
          | exact superpose b2e830 b2e32
          | exact resolve b2e32 b2e830
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e3756 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ x) X1) (σ x))) = (M.op y (M.op (M.op (M.op y (σ y)) X0) (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b2e3730 X0 X1
             have i₂ := b2e155 (σ y) (M.op (M.op y (σ y)) X0)
             grind)
          | exact superpose b2e155 b2e3730
          | exact resolve b2e3730 b2e155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3730
        have b2e3766 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ x) X1) (σ x))) = (M.op y (M.op (M.op y X0) (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b2e3756 X0 X1
             have i₂ := b2e152 (σ y) X0
             grind)
          | exact superpose b2e152 b2e3756
          | exact resolve b2e3756 b2e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3756
        have b2e3770 : ∀ X1 : G, (M.op (σ x) (M.op (M.op (σ x) X1) (σ x))) = (M.op y (M.op y (σ y))) := by
          intro X1
          first
          | (have i₁ := b2e3766 x X1
             have i₂ := b2e152 x (σ y)
             grind)
          | exact superpose b2e152 b2e3766
          | exact resolve b2e3766 b2e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e152 b2e3766
        have b2e3771 : ∀ X1 : G, (M.op y (σ y)) = (M.op (σ x) (M.op (M.op (σ x) X1) (σ x))) := by
          intro X1
          first
          | (have i₁ := b2e3770 X1
             have i₂ := b2e45 y (σ y)
             grind)
          | exact superpose b2e45 b2e3770
          | exact resolve b2e3770 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3770
        have b2e3772 : (M.op y (σ y)) = (M.op (σ x) (M.op y (σ x))) := by
          first
          | (have i₁ := b2e3771 x
             have i₂ := b2e109 (σ x) x
             grind)
          | exact superpose b2e109 b2e3771
          | exact resolve b2e3771 b2e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e109 b2e3771
        have b2e3773 : (M.op y (σ y)) = (M.op y (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b2e3772
             have i₂ := b2e155 (σ x) (σ x)
             grind)
          | exact superpose b2e155 b2e3772
          | exact resolve b2e3772 b2e155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e155 b2e3772
        have b2e3774 : (M.op y (σ y)) = (M.op y (M.op y (σ x))) := by
          first
          | (have i₁ := b2e3773
             have i₂ := b2e831
             grind)
          | exact superpose b2e831 b2e3773
          | exact resolve b2e3773 b2e831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e831 b2e3773
        have b2e3775 : (M.op y (σ y)) = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e3774
             have i₂ := b2e45 y (σ x)
             grind)
          | exact superpose b2e45 b2e3774
          | exact resolve b2e3774 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45 b2e3774
        have b2e4541 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op y (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e3447
             have i₂ := b2e15 x x
             grind)
          | exact superpose b2e15 b2e3447
          | (have j1 := b2e15 x x
             grind)
          | exact resolve b2e3447 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e4542 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op y (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e4541
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e4541
          | exact resolve b2e4541 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4541
        have b2e4543 : (σ x) = (M.op y (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e4542
        have b2e4552 : (σ x) = (M.op y (σ y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e4543
             have i₂ := b2e3775
             grind)
          | exact superpose b2e3775 b2e4543
          | exact resolve b2e4543 b2e3775
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4543
        have b2e4557 : (σ x) = (M.op y (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e4552
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e4552
          | exact resolve b2e4552 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4552
        have b2e4564 : x = (k x (τ (M.op y (σ y)))) := by
          first
          | (have i₁ := b2e3522 x
             have i₂ := b2e830
             grind)
          | exact superpose b2e830 b2e3522
          | exact resolve b2e3522 b2e830
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e830 b2e3522
        have b2e4992 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e4564
             have i₂ := b2e4557
             grind)
          | exact superpose b2e4557 b2e4564
          | exact resolve b2e4564 b2e4557
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4557 b2e4564
        have b2e5030 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e4992
             have i₂ := b2e12 x
             grind)
          | exact superpose b2e12 b2e4992
          | exact resolve b2e4992 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4992
        have b2e5034 : x = (k x x) := by
          first
          | (have r₁ := b2e5030
             have r₂ := b2e3556
             grind)
          | exact resolve b2e5030 b2e3556
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3556 b2e5030
        have b2e5103 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e3447
             have i₂ := b2e5034
             grind)
          | exact superpose b2e5034 b2e3447
          | exact resolve b2e3447 b2e5034
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3447
        have b2e5107 : x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e15 x x
             have i₂ := b2e5034
             grind)
          | exact superpose b2e5034 b2e15
          | (have j0 := b2e15 x x
             grind)
          | exact resolve b2e15 b2e5034
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5034
        have b2e5108 : x = (M.op x x) := by grind
        clear b2e5107
        have b2e5110 : x = y := by
          first
          | (have i₁ := b2e5108
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e5108
          | exact resolve b2e5108 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5108
        have b2e5114 : (σ x) = (M.op y (σ y)) ∨ (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e5103
             have i₂ := b2e3775
             grind)
          | exact superpose b2e3775 b2e5103
          | exact resolve b2e5103 b2e3775
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3775 b2e5103
        have b2e5119 : (σ y) = (M.op y (σ y)) ∨ (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e5114
             have i₂ := b2e5110
             grind)
          | exact superpose b2e5110 b2e5114
          | exact resolve b2e5114 b2e5110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5114
        have b2e5120 : (σ x) ≠ (σ y) := by
          first
          | (have r₁ := b2e5119
             have r₂ := b2e3723
             grind)
          | exact resolve b2e5119 b2e3723
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3723 b2e5119
        have b2e5121 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e5120
             have i₂ := b2e5110
             grind)
          | exact superpose b2e5110 b2e5120
          | exact resolve b2e5120 b2e5110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5110 b2e5120
        have b2e5122 : False := by grind
        exact b2e5122
      · have b3e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
        have b3e42 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b3e70 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b3e205 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e42 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e211 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b3e70
        have b3e225 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e211 X0
             have i₂ := b3e12 X0
             grind)
          | exact superpose b3e12 b3e211
          | exact resolve b3e211 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e211
        have b3e317 : x ≠ y ∨ x = (k x x) := by
          first
          | (have i₁ := b3e205 x x
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e205
          | (have j0 := b3e205 x x
             grind)
          | exact resolve b3e205 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e205
        have b3e1613 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e47 x x
             grind)
          | exact superpose b3e47 b3e19
          | (have j1 := b3e47 x x
             grind)
          | (have r₁ := b3e19
             have r₂ := b3e47 x y
             grind)
          | exact resolve b3e19 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1672 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b3e47 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e50077 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e1613
             have i₂ := b3e15 x x
             grind)
          | exact superpose b3e15 b3e1613
          | (have j1 := b3e15 (σ x) (σ x)
             grind)
          | exact resolve b3e1613 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1613
        have b3e50078 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e50077
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e50077
          | exact resolve b3e50077 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50077
        have b3e50079 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b3e50078
        have b3e50092 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b3e50079
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e50079
          | exact resolve b3e50079 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50079
        have b3e50105 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b3e225 x
             have i₂ := b3e50092
             grind)
          | exact superpose b3e50092 b3e225
          | exact resolve b3e225 b3e50092
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e225 b3e50092
        have b3e50213 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b3e50105
             have i₂ := b3e12 x
             grind)
          | exact superpose b3e12 b3e50105
          | exact resolve b3e50105 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50105
        have b3e50220 : x = (k x x) := by
          first
          | (have r₁ := b3e50213
             have r₂ := b3e317
             grind)
          | exact resolve b3e50213 b3e317
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e317 b3e50213
        have b3e50245 : x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e15 x x
             have i₂ := b3e50220
             grind)
          | exact superpose b3e50220 b3e15
          | (have j0 := b3e15 x x
             grind)
          | exact resolve b3e15 b3e50220
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e50246 : x = (M.op x x) := by grind
        clear b3e50245
        have b3e50248 : x = y := by
          first
          | (have i₁ := b3e50246
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e50246
          | exact resolve b3e50246 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50246
        have b3e50270 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e1672 x
             have i₂ := b3e50220
             grind)
          | exact superpose b3e50220 b3e1672
          | (have j0 := b3e1672 x
             grind)
          | exact resolve b3e1672 b3e50220
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1672 b3e50220
        have b3e50277 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b3e50270
        have b3e50283 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e50277
             have i₂ := b3e50248
             grind)
          | exact superpose b3e50248 b3e50277
          | exact resolve b3e50277 b3e50248
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50277
        have b3e50292 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e50248
             grind)
          | exact superpose b3e50248 b3e19
          | exact resolve b3e19 b3e50248
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50248
        have b3e50374 : False := by grind
        exact b3e50374
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b4e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          grind
        have b4e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b4e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b4e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
        have b4e40 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 y)) := by
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
        have b4e42 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b4e40 X0
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e40
          | exact resolve b4e40 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e40
        have b4e60 : x = (M.op x y) ∨ y = (M.op x x) := by
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
        have b4e66 : x = (M.op x y) := by
          first
          | (have r₁ := b4e60
             have r₂ := b4e18
             grind)
          | exact resolve b4e60 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e60
        have b4e69 : y = (M.op x x) := by
          first
          | (have i₁ := b4e42 x
             have i₂ := b4e66
             grind)
          | exact superpose b4e66 b4e42
          | exact resolve b4e42 b4e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e42 b4e66
        have b4e72 : False := by grind
        exact b4e72
      · have b5e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b5e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b5e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
        have b5e58 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b5e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b5e65 : x = (M.op x y) ∨ y = (M.op x x) := by
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
        have b5e68 : x = (M.op x y) := by
          first
          | (have r₁ := b5e65
             have r₂ := b5e18
             grind)
          | exact resolve b5e65 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e65
        have b5e1665 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e63 x x
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e63
          | exact resolve b5e63 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e63
        have b5e1832 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e12 (k x x)
             have i₂ := b5e1665
             grind)
          | exact superpose b5e1665 b5e12
          | exact resolve b5e12 b5e1665
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1665
        have b5e1845 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e1832
             have i₂ := b5e12 y
             grind)
          | exact superpose b5e12 b5e1832
          | exact resolve b5e1832 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1832
        have b5e2148 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e58 x x
             have i₂ := b5e1845
             grind)
          | exact superpose b5e1845 b5e58
          | exact resolve b5e58 b5e1845
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e58 b5e1845
        have b5e2151 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have r₁ := b5e2148
             have r₂ := b5e18
             grind)
          | exact resolve b5e2148 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e2148
        have b5e2240 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b5e12 x
             have i₂ := b5e2151
             grind)
          | exact superpose b5e2151 b5e12
          | exact resolve b5e12 b5e2151
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e2151
        have b5e2253 : x = y ∨ x = y := by
          first
          | (have i₁ := b5e2240
             have i₂ := b5e12 y
             grind)
          | exact superpose b5e12 b5e2240
          | exact resolve b5e2240 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e2240
        have b5e2254 : x = y := by grind
        clear b5e2253
        have b5e2661 : y = (M.op y y) := by
          first
          | (have i₁ := b5e68
             have i₂ := b5e2254
             grind)
          | exact superpose b5e2254 b5e68
          | exact resolve b5e68 b5e2254
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e68 b5e2254
        have b5e2670 : False := by grind
        exact b5e2670
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e18 : y ≠ (M.op x x) := by grind
        have b6e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b6e46 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
        have b6e856 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b6e46 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46
        have b6e857 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e856
             have i₂ := b6e16 x y
             grind)
          | exact superpose b6e16 b6e856
          | exact resolve b6e856 b6e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e856
        have b6e2261 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e17
             have i₂ := b6e857
             grind)
          | exact superpose b6e857 b6e17
          | exact resolve b6e17 b6e857
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e857
        have b6e2952 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e2261
             have i₂ := b6e15 x y
             grind)
          | exact superpose b6e15 b6e2261
          | (have j1 := b6e15 x y
             grind)
          | exact resolve b6e2261 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2261
        have b6e2953 : y = (M.op x x) := by grind
        clear b6e2952
        have b6e2955 : False := by grind
        exact b6e2955
      · have b7e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b7e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b7e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b7e18 : y ≠ (M.op x x) := by grind
        have b7e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b7e49 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
        have b7e243 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b7e49 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e49
        have b7e244 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b7e243
             have i₂ := b7e16 x y
             grind)
          | exact superpose b7e16 b7e243
          | exact resolve b7e243 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e243
        have b7e245 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e244
             grind)
          | exact superpose b7e244 b7e17
          | exact resolve b7e17 b7e244
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e244
        have b7e340 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b7e245
             have i₂ := b7e15 x y
             grind)
          | exact superpose b7e15 b7e245
          | (have j1 := b7e15 x y
             grind)
          | exact resolve b7e245 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e245
        have b7e341 : y = (M.op x x) := by grind
        clear b7e340
        have b7e343 : False := by grind
        exact b7e343
